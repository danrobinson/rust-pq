#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

@interface SlhMetalCtxObj : NSObject
@property(nonatomic, strong) id<MTLDevice> device;
@property(nonatomic, strong) id<MTLCommandQueue> queue;
@property(nonatomic, strong) id<MTLLibrary> library;
@end
@implementation SlhMetalCtxObj
@end

@interface SlhMetalPipelineObj : NSObject
@property(nonatomic, strong) id<MTLComputePipelineState> state;
@end
@implementation SlhMetalPipelineObj
@end

@interface SlhMetalBufferObj : NSObject
@property(nonatomic, strong) id<MTLBuffer> buffer;
@property(nonatomic, assign) size_t requestedLen;
@end
@implementation SlhMetalBufferObj
@end

@interface SlhMetalCmdObj : NSObject
@property(nonatomic, strong) id<MTLCommandBuffer> cmdBuf;
@property(nonatomic, strong) id<MTLComputeCommandEncoder> encoder;
@property(nonatomic, assign) bool concurrent;
@end
@implementation SlhMetalCmdObj
@end

typedef struct SlhMetalCtx SlhMetalCtx;
typedef struct SlhMetalPipeline SlhMetalPipeline;
typedef struct SlhMetalBuffer SlhMetalBuffer;
typedef struct SlhMetalCmd SlhMetalCmd;

static void write_err(char *err_buf, size_t err_cap, NSString *msg) {
    if (!err_buf || err_cap == 0) {
        return;
    }
    const char *utf8 = msg ? [msg UTF8String] : "unknown Metal error";
    if (!utf8) {
        utf8 = "unknown Metal error";
    }
    strncpy(err_buf, utf8, err_cap - 1);
    err_buf[err_cap - 1] = '\0';
}

SlhMetalCtx *slh_metal_ctx_create(
    const char *shader_src,
    size_t shader_len,
    char *err_buf,
    size_t err_cap
) {
    @autoreleasepool {
        id<MTLDevice> device = MTLCreateSystemDefaultDevice();
        if (!device) {
            write_err(err_buf, err_cap, @"MTLCreateSystemDefaultDevice() returned nil");
            return NULL;
        }
        id<MTLCommandQueue> queue = [device newCommandQueue];
        if (!queue) {
            write_err(err_buf, err_cap, @"failed to create MTLCommandQueue");
            return NULL;
        }
        NSString *source = [[NSString alloc] initWithBytes:shader_src
                                                    length:shader_len
                                                  encoding:NSUTF8StringEncoding];
        if (!source) {
            write_err(err_buf, err_cap, @"shader source is not valid UTF-8");
            return NULL;
        }
        MTLCompileOptions *opts = [[MTLCompileOptions alloc] init];
        NSError *error = nil;
        id<MTLLibrary> library = [device newLibraryWithSource:source options:opts error:&error];
        if (!library) {
            write_err(err_buf, err_cap, error ? [error localizedDescription] : @"shader compilation failed");
            return NULL;
        }
        SlhMetalCtxObj *obj = [[SlhMetalCtxObj alloc] init];
        obj.device = device;
        obj.queue = queue;
        obj.library = library;
        return (__bridge_retained SlhMetalCtx *)obj;
    }
}

void slh_metal_ctx_destroy(SlhMetalCtx *ctx) {
    if (!ctx) {
        return;
    }
    @autoreleasepool {
        SlhMetalCtxObj *obj = (__bridge_transfer SlhMetalCtxObj *)ctx;
        (void)obj;
    }
}

void slh_metal_ctx_device_name(const SlhMetalCtx *ctx, char *buf, size_t cap) {
    if (!ctx || !buf || cap == 0) {
        return;
    }
    @autoreleasepool {
        SlhMetalCtxObj *obj = (__bridge SlhMetalCtxObj *)ctx;
        const char *name = [[obj.device name] UTF8String];
        if (!name) {
            name = "Unknown Apple GPU";
        }
        strncpy(buf, name, cap - 1);
        buf[cap - 1] = '\0';
    }
}

bool slh_metal_ctx_has_unified_memory(const SlhMetalCtx *ctx) {
    if (!ctx) {
        return false;
    }
    @autoreleasepool {
        SlhMetalCtxObj *obj = (__bridge SlhMetalCtxObj *)ctx;
        return [obj.device hasUnifiedMemory] ? true : false;
    }
}

SlhMetalPipeline *slh_metal_pipeline_create(
    const SlhMetalCtx *ctx,
    const char *fn_name,
    char *err_buf,
    size_t err_cap
) {
    if (!ctx || !fn_name) {
        write_err(err_buf, err_cap, @"null argument to slh_metal_pipeline_create");
        return NULL;
    }
    @autoreleasepool {
        SlhMetalCtxObj *obj = (__bridge SlhMetalCtxObj *)ctx;
        NSString *name = [NSString stringWithUTF8String:fn_name];
        id<MTLFunction> fn = [obj.library newFunctionWithName:name];
        if (!fn) {
            write_err(err_buf, err_cap, [NSString stringWithFormat:@"Metal function not found: %@", name]);
            return NULL;
        }
        NSError *error = nil;
        id<MTLComputePipelineState> state = [obj.device newComputePipelineStateWithFunction:fn error:&error];
        if (!state) {
            write_err(err_buf, err_cap, error ? [error localizedDescription] : @"pipeline creation failed");
            return NULL;
        }
        SlhMetalPipelineObj *p = [[SlhMetalPipelineObj alloc] init];
        p.state = state;
        return (__bridge_retained SlhMetalPipeline *)p;
    }
}

void slh_metal_pipeline_destroy(SlhMetalPipeline *p) {
    if (!p) {
        return;
    }
    @autoreleasepool {
        SlhMetalPipelineObj *obj = (__bridge_transfer SlhMetalPipelineObj *)p;
        (void)obj;
    }
}

uint32_t slh_metal_pipeline_max_tg_size(const SlhMetalPipeline *p) {
    if (!p) {
        return 0;
    }
    @autoreleasepool {
        SlhMetalPipelineObj *obj = (__bridge SlhMetalPipelineObj *)p;
        return (uint32_t)[obj.state maxTotalThreadsPerThreadgroup];
    }
}

uint32_t slh_metal_pipeline_simd_width(const SlhMetalPipeline *p) {
    if (!p) {
        return 32;
    }
    @autoreleasepool {
        SlhMetalPipelineObj *obj = (__bridge SlhMetalPipelineObj *)p;
        return (uint32_t)[obj.state threadExecutionWidth];
    }
}

SlhMetalBuffer *slh_metal_buffer_alloc(const SlhMetalCtx *ctx, size_t len) {
    if (!ctx) {
        return NULL;
    }
    @autoreleasepool {
        SlhMetalCtxObj *obj = (__bridge SlhMetalCtxObj *)ctx;
        size_t alloc_len = (len == 0) ? 16 : len;
        id<MTLBuffer> buf = [obj.device newBufferWithLength:alloc_len
                                                    options:MTLResourceStorageModeShared];
        if (!buf) {
            return NULL;
        }
        SlhMetalBufferObj *b = [[SlhMetalBufferObj alloc] init];
        b.buffer = buf;
        b.requestedLen = len;
        return (__bridge_retained SlhMetalBuffer *)b;
    }
}

void *slh_metal_buffer_contents(const SlhMetalBuffer *buf) {
    if (!buf) {
        return NULL;
    }
    SlhMetalBufferObj *obj = (__bridge SlhMetalBufferObj *)buf;
    return [obj.buffer contents];
}

size_t slh_metal_buffer_length(const SlhMetalBuffer *buf) {
    if (!buf) {
        return 0;
    }
    SlhMetalBufferObj *obj = (__bridge SlhMetalBufferObj *)buf;
    return obj.requestedLen;
}

void slh_metal_buffer_destroy(SlhMetalBuffer *buf) {
    if (!buf) {
        return;
    }
    @autoreleasepool {
        SlhMetalBufferObj *obj = (__bridge_transfer SlhMetalBufferObj *)buf;
        (void)obj;
    }
}

SlhMetalCmd *slh_metal_cmd_begin(const SlhMetalCtx *ctx, bool concurrent) {
    if (!ctx) {
        return NULL;
    }
    @autoreleasepool {
        SlhMetalCtxObj *obj = (__bridge SlhMetalCtxObj *)ctx;
        id<MTLCommandBuffer> cmdBuf = [obj.queue commandBuffer];
        if (!cmdBuf) {
            return NULL;
        }
        id<MTLComputeCommandEncoder> encoder = concurrent
            ? [cmdBuf computeCommandEncoderWithDispatchType:MTLDispatchTypeConcurrent]
            : [cmdBuf computeCommandEncoder];
        if (!encoder) {
            return NULL;
        }
        SlhMetalCmdObj *cmd = [[SlhMetalCmdObj alloc] init];
        cmd.cmdBuf = cmdBuf;
        cmd.encoder = encoder;
        cmd.concurrent = concurrent;
        return (__bridge_retained SlhMetalCmd *)cmd;
    }
}

void slh_metal_cmd_barrier(SlhMetalCmd *cmd) {
    if (!cmd) {
        return;
    }
    @autoreleasepool {
        SlhMetalCmdObj *obj = (__bridge SlhMetalCmdObj *)cmd;
        if (obj.concurrent) {
            [obj.encoder memoryBarrierWithScope:MTLBarrierScopeBuffers];
        }
    }
}

void slh_metal_cmd_dispatch(
    SlhMetalCmd *cmd,
    const SlhMetalPipeline *pipeline,
    const SlhMetalBuffer *const *buffers,
    uint32_t num_buffers,
    const void *const *bytes_ptrs,
    const uint32_t *bytes_lens,
    const uint32_t *bytes_indices,
    uint32_t num_bytes,
    uint32_t grid_x,
    uint32_t tg_x,
    uint32_t tg_mem_len,
    bool use_threadgroups
) {
    if (!cmd || !pipeline || grid_x == 0 || tg_x == 0) {
        return;
    }
    @autoreleasepool {
        SlhMetalCmdObj *cmdObj = (__bridge SlhMetalCmdObj *)cmd;
        SlhMetalPipelineObj *pipeObj = (__bridge SlhMetalPipelineObj *)pipeline;
        id<MTLComputeCommandEncoder> enc = cmdObj.encoder;

        [enc setComputePipelineState:pipeObj.state];
        for (uint32_t i = 0; i < num_buffers; ++i) {
            if (buffers[i]) {
                SlhMetalBufferObj *bufObj = (__bridge SlhMetalBufferObj *)buffers[i];
                [enc setBuffer:bufObj.buffer offset:0 atIndex:i];
            }
        }
        for (uint32_t i = 0; i < num_bytes; ++i) {
            [enc setBytes:bytes_ptrs[i] length:bytes_lens[i] atIndex:bytes_indices[i]];
        }
        if (tg_mem_len > 0) {
            [enc setThreadgroupMemoryLength:tg_mem_len atIndex:0];
        }
        MTLSize tgSize = MTLSizeMake(tg_x, 1, 1);
        if (use_threadgroups) {
            MTLSize numTgs = MTLSizeMake(grid_x, 1, 1);
            [enc dispatchThreadgroups:numTgs threadsPerThreadgroup:tgSize];
        } else {
            MTLSize gridSize = MTLSizeMake(grid_x, 1, 1);
            [enc dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        }
    }
}

int slh_metal_cmd_commit_and_wait(SlhMetalCmd *cmd, char *err_buf, size_t err_cap) {
    if (!cmd) {
        write_err(err_buf, err_cap, @"null command buffer");
        return -1;
    }
    @autoreleasepool {
        SlhMetalCmdObj *obj = (__bridge_transfer SlhMetalCmdObj *)cmd;
        [obj.encoder endEncoding];
        [obj.cmdBuf commit];
        [obj.cmdBuf waitUntilCompleted];
        if ([obj.cmdBuf status] != MTLCommandBufferStatusCompleted) {
            NSError *err = [obj.cmdBuf error];
            write_err(err_buf, err_cap, err ? [err localizedDescription] : @"Metal command buffer failed");
            return -1;
        }
        return 0;
    }
}
