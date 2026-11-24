//! Safe RAII Rust wrapper over the Objective-C Metal compute bridge.

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int, c_void};
use std::ptr::NonNull;
use std::slice;
use zeroize::Zeroize;

#[repr(C)]
struct SlhMetalCtx {
    _private: [u8; 0],
}
#[repr(C)]
struct SlhMetalPipeline {
    _private: [u8; 0],
}
#[repr(C)]
struct SlhMetalBuffer {
    _private: [u8; 0],
}
#[repr(C)]
struct SlhMetalCmd {
    _private: [u8; 0],
}

extern "C" {
    fn slh_metal_ctx_create(
        shader_src: *const c_char,
        shader_len: usize,
        err_buf: *mut c_char,
        err_cap: usize,
    ) -> *mut SlhMetalCtx;
    fn slh_metal_ctx_destroy(ctx: *mut SlhMetalCtx);
    fn slh_metal_ctx_device_name(ctx: *const SlhMetalCtx, buf: *mut c_char, cap: usize);
    fn slh_metal_ctx_has_unified_memory(ctx: *const SlhMetalCtx) -> bool;

    fn slh_metal_pipeline_create(
        ctx: *const SlhMetalCtx,
        fn_name: *const c_char,
        err_buf: *mut c_char,
        err_cap: usize,
    ) -> *mut SlhMetalPipeline;
    fn slh_metal_pipeline_destroy(p: *mut SlhMetalPipeline);
    fn slh_metal_pipeline_max_tg_size(p: *const SlhMetalPipeline) -> u32;
    fn slh_metal_pipeline_simd_width(p: *const SlhMetalPipeline) -> u32;

    fn slh_metal_buffer_alloc(ctx: *const SlhMetalCtx, len: usize) -> *mut SlhMetalBuffer;
    fn slh_metal_buffer_contents(buf: *const SlhMetalBuffer) -> *mut c_void;
    fn slh_metal_buffer_length(buf: *const SlhMetalBuffer) -> usize;
    fn slh_metal_buffer_destroy(buf: *mut SlhMetalBuffer);

    fn slh_metal_cmd_begin(ctx: *const SlhMetalCtx, concurrent: bool) -> *mut SlhMetalCmd;
    fn slh_metal_cmd_barrier(cmd: *mut SlhMetalCmd);
    fn slh_metal_cmd_dispatch(
        cmd: *mut SlhMetalCmd,
        pipeline: *const SlhMetalPipeline,
        buffers: *const *const SlhMetalBuffer,
        num_buffers: u32,
        bytes_ptrs: *const *const c_void,
        bytes_lens: *const u32,
        bytes_indices: *const u32,
        num_bytes: u32,
        grid_x: u32,
        tg_x: u32,
        tg_mem_len: u32,
        use_threadgroups: bool,
    );
    fn slh_metal_cmd_commit_and_wait(
        cmd: *mut SlhMetalCmd,
        err_buf: *mut c_char,
        err_cap: usize,
    ) -> c_int;
}

/// Error returned by Metal GPU operations.
#[derive(Debug, Clone)]
pub struct MetalError(pub String);

impl std::fmt::Display for MetalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MetalError: {}", self.0)
    }
}

impl std::error::Error for MetalError {}

fn read_err_buf(buf: &[c_char]) -> String {
    unsafe { CStr::from_ptr(buf.as_ptr()) }
        .to_string_lossy()
        .into_owned()
}

/// Owned Metal device + command queue + compiled shader library.
pub struct MetalContext {
    raw: NonNull<SlhMetalCtx>,
}

// Metal devices, queues, and libraries are thread-safe in Apple's Metal API.
unsafe impl Send for MetalContext {}
unsafe impl Sync for MetalContext {}

impl MetalContext {
    pub fn new(shader_src: &str) -> Result<Self, MetalError> {
        let mut err = [0 as c_char; 1024];
        let raw = unsafe {
            slh_metal_ctx_create(
                shader_src.as_ptr() as *const c_char,
                shader_src.len(),
                err.as_mut_ptr(),
                err.len(),
            )
        };
        NonNull::new(raw)
            .map(|raw| Self { raw })
            .ok_or_else(|| MetalError(read_err_buf(&err)))
    }

    pub fn device_name(&self) -> String {
        let mut buf = [0 as c_char; 256];
        unsafe { slh_metal_ctx_device_name(self.raw.as_ptr(), buf.as_mut_ptr(), buf.len()) };
        read_err_buf(&buf)
    }

    pub fn has_unified_memory(&self) -> bool {
        unsafe { slh_metal_ctx_has_unified_memory(self.raw.as_ptr()) }
    }

    pub fn pipeline(&self, fn_name: &str) -> Result<MetalPipeline, MetalError> {
        let c_name = CString::new(fn_name).map_err(|e| MetalError(e.to_string()))?;
        let mut err = [0 as c_char; 512];
        let raw = unsafe {
            slh_metal_pipeline_create(
                self.raw.as_ptr(),
                c_name.as_ptr(),
                err.as_mut_ptr(),
                err.len(),
            )
        };
        NonNull::new(raw)
            .map(|raw| MetalPipeline { raw })
            .ok_or_else(|| MetalError(read_err_buf(&err)))
    }

    pub fn alloc_buffer(&self, len: usize) -> Result<MetalBuffer, MetalError> {
        let raw = unsafe { slh_metal_buffer_alloc(self.raw.as_ptr(), len) };
        NonNull::new(raw)
            .map(|raw| MetalBuffer {
                raw,
                zeroize_on_drop: false,
            })
            .ok_or_else(|| MetalError(format!("failed to allocate Metal shared buffer ({len} bytes)")))
    }

    /// Allocates a Unified Memory buffer that automatically zeroizes its
    /// contents when dropped (for `SK.seed` and other secret material).
    pub fn alloc_secret_buffer(&self, len: usize) -> Result<MetalBuffer, MetalError> {
        let mut buf = self.alloc_buffer(len)?;
        buf.zeroize_on_drop = true;
        Ok(buf)
    }

    pub fn begin_cmd(&self, concurrent: bool) -> Result<MetalCommand, MetalError> {
        let raw = unsafe { slh_metal_cmd_begin(self.raw.as_ptr(), concurrent) };
        NonNull::new(raw)
            .map(|raw| MetalCommand { raw: Some(raw) })
            .ok_or_else(|| MetalError("failed to create Metal command buffer".to_string()))
    }
}

impl Drop for MetalContext {
    fn drop(&mut self) {
        unsafe { slh_metal_ctx_destroy(self.raw.as_ptr()) };
    }
}

/// Compiled `MTLComputePipelineState`.
pub struct MetalPipeline {
    raw: NonNull<SlhMetalPipeline>,
}

unsafe impl Send for MetalPipeline {}
unsafe impl Sync for MetalPipeline {}

impl MetalPipeline {
    pub fn max_tg_size(&self) -> u32 {
        unsafe { slh_metal_pipeline_max_tg_size(self.raw.as_ptr()) }
    }

    pub fn simd_width(&self) -> u32 {
        unsafe { slh_metal_pipeline_simd_width(self.raw.as_ptr()) }
    }
}

impl Drop for MetalPipeline {
    fn drop(&mut self) {
        unsafe { slh_metal_pipeline_destroy(self.raw.as_ptr()) };
    }
}

/// Shared Unified Memory (`MTLResourceStorageModeShared`) buffer with RAII cleanup.
pub struct MetalBuffer {
    raw: NonNull<SlhMetalBuffer>,
    zeroize_on_drop: bool,
}

unsafe impl Send for MetalBuffer {}

impl MetalBuffer {
    pub fn len(&self) -> usize {
        unsafe { slh_metal_buffer_length(self.raw.as_ptr()) }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn as_slice(&self) -> &[u8] {
        let len = self.len();
        if len == 0 {
            return &[];
        }
        unsafe {
            let ptr = slh_metal_buffer_contents(self.raw.as_ptr()) as *const u8;
            slice::from_raw_parts(ptr, len)
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        let len = self.len();
        if len == 0 {
            return &mut [];
        }
        unsafe {
            let ptr = slh_metal_buffer_contents(self.raw.as_ptr()) as *mut u8;
            slice::from_raw_parts_mut(ptr, len)
        }
    }

    /// Borrows the prefix as aligned shader records. A record has no padding
    /// and every bit pattern is valid, including bytes written by the GPU.
    pub fn as_mut_slice_of<T: bytemuck::Pod>(&mut self, count: usize) -> &mut [T] {
        if count == 0 {
            return &mut [];
        }
        let len = count.checked_mul(std::mem::size_of::<T>()).expect("record size overflow");
        assert!(len > 0, "shader records must have a positive size");
        bytemuck::cast_slice_mut(&mut self.as_mut_slice()[..len])
    }

    /// Borrows the prefix as aligned shader records.
    pub fn as_slice_of<T: bytemuck::Pod>(&self, count: usize) -> &[T] {
        if count == 0 {
            return &[];
        }
        let len = count.checked_mul(std::mem::size_of::<T>()).expect("record size overflow");
        assert!(len > 0, "shader records must have a positive size");
        bytemuck::cast_slice(&self.as_slice()[..len])
    }

    /// Overwrites the entire backing memory with zeros using `zeroize`.
    pub fn zeroize_contents(&mut self) {
        self.as_mut_slice().zeroize();
    }
}

impl Drop for MetalBuffer {
    fn drop(&mut self) {
        if self.zeroize_on_drop {
            self.zeroize_contents();
        }
        unsafe { slh_metal_buffer_destroy(self.raw.as_ptr()) };
    }
}

/// Inline constant bytes bound to a kernel buffer slot via `setBytes`.
pub struct InlineBytes<'a> {
    pub index: u32,
    pub data: &'a [u8],
}

impl<'a> InlineBytes<'a> {
    pub fn of<T: bytemuck::NoUninit>(index: u32, val: &'a T) -> Self {
        let data = bytemuck::bytes_of(val);
        Self { index, data }
    }
}

/// Active Metal command buffer + compute encoder.
pub struct MetalCommand {
    raw: Option<NonNull<SlhMetalCmd>>,
}

impl MetalCommand {
    pub fn barrier(&mut self) {
        if let Some(raw) = self.raw {
            unsafe { slh_metal_cmd_barrier(raw.as_ptr()) };
        }
    }

    /// Dispatches exact `grid_x` threads with threadgroup size `tg_x`.
    pub fn dispatch_threads(
        &mut self,
        pipeline: &MetalPipeline,
        buffers: &[&MetalBuffer],
        inline_bytes: &[InlineBytes<'_>],
        grid_x: u32,
        tg_x: u32,
        tg_mem_len: u32,
    ) {
        self.dispatch_impl(pipeline, buffers, inline_bytes, grid_x, tg_x, tg_mem_len, false);
    }

    /// Dispatches `num_tgs` threadgroups, each with `tg_x` threads.
    pub fn dispatch_threadgroups(
        &mut self,
        pipeline: &MetalPipeline,
        buffers: &[&MetalBuffer],
        inline_bytes: &[InlineBytes<'_>],
        num_tgs: u32,
        tg_x: u32,
        tg_mem_len: u32,
    ) {
        self.dispatch_impl(pipeline, buffers, inline_bytes, num_tgs, tg_x, tg_mem_len, true);
    }

    #[allow(clippy::too_many_arguments)]
    fn dispatch_impl(
        &mut self,
        pipeline: &MetalPipeline,
        buffers: &[&MetalBuffer],
        inline_bytes: &[InlineBytes<'_>],
        grid_x: u32,
        tg_x: u32,
        tg_mem_len: u32,
        use_threadgroups: bool,
    ) {
        let Some(raw) = self.raw else {
            return;
        };
        assert!(buffers.len() <= 16 && inline_bytes.len() <= 8);
        let mut buf_ptrs = [std::ptr::null::<SlhMetalBuffer>(); 16];
        for (dst, b) in buf_ptrs.iter_mut().zip(buffers.iter()) {
            *dst = b.raw.as_ptr() as *const SlhMetalBuffer;
        }
        let mut byte_ptrs = [std::ptr::null::<c_void>(); 8];
        let mut byte_lens = [0u32; 8];
        let mut byte_indices = [0u32; 8];
        for (i, b) in inline_bytes.iter().enumerate() {
            byte_ptrs[i] = b.data.as_ptr() as *const c_void;
            byte_lens[i] = b.data.len() as u32;
            byte_indices[i] = b.index;
        }

        unsafe {
            slh_metal_cmd_dispatch(
                raw.as_ptr(),
                pipeline.raw.as_ptr(),
                buf_ptrs.as_ptr(),
                buffers.len() as u32,
                byte_ptrs.as_ptr(),
                byte_lens.as_ptr(),
                byte_indices.as_ptr(),
                inline_bytes.len() as u32,
                grid_x,
                tg_x,
                tg_mem_len,
                use_threadgroups,
            );
        }
    }

    pub fn commit_and_wait(mut self) -> Result<(), MetalError> {
        let raw = self
            .raw
            .take()
            .ok_or_else(|| MetalError("command already committed".to_string()))?;
        let mut err = [0 as c_char; 512];
        let rc = unsafe { slh_metal_cmd_commit_and_wait(raw.as_ptr(), err.as_mut_ptr(), err.len()) };
        if rc == 0 {
            Ok(())
        } else {
            Err(MetalError(read_err_buf(&err)))
        }
    }
}

impl Drop for MetalCommand {
    fn drop(&mut self) {
        if let Some(raw) = self.raw.take() {
            let mut err = [0 as c_char; 16];
            unsafe {
                let _ = slh_metal_cmd_commit_and_wait(raw.as_ptr(), err.as_mut_ptr(), err.len());
            }
        }
    }
}
