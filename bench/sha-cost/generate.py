"""Emit standalone C microbenchmarks. Compile with -O3 -march=native and libcrypto."""
import re
from pathlib import Path

root = Path(__file__).resolve().parents[2]
print('''
#define OPENSSL_SUPPRESS_DEPRECATED
#include <openssl/sha.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#if defined(__aarch64__)
#include <arm_neon.h>
#elif defined(__x86_64__)
#include <immintrin.h>
#endif
static uint8_t input[16][128];
static uint32_t s256[16][8];
static uint64_t s512[16][8];
static uint8_t buf[16384];
static double ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return 1e9*t.tv_sec+t.tv_nsec; }
#define NOINLINE __attribute__((noinline))
''')
cases = []
for bits, w, rounds, step in [(256,32,64,64),(512,64,80,128)]:
    typ = f'uint{w}_t'
    src = (root / f'rust/src/sha{bits}.rs').read_text().split('const K:',1)[1].split('= [',1)[1].split('];',1)[0]
    constants = re.findall(r'0x[\da-f_]+',src)
    assert len(constants) == rounds
    print(f'static const {typ} k{bits}[] = {{'+','.join(x.replace('_','') for x in constants)+'};')
    ctx = f'SHA{bits}_CTX'
    print(f'''
static {ctx} stream{bits};
static NOINLINE void bulk{bits}(void) {{ SHA{bits}_Update(&stream{bits},buf,sizeof(buf)); }}
static void check{bits}(int lanes) {{
  for(int i=0;i<lanes;i++) {{
    {ctx} ref; SHA{bits}_Init(&ref);
    for(int j=0;j<8;j++) ref.h[j]=37*i+j;
    SHA{bits}_Transform(&ref,input[i]);
    if(memcmp(ref.h,s{bits}[i],sizeof(ref.h))) {{ fprintf(stderr,"bad SHA-{bits} lane %d\\n",i); abort(); }}
  }}
}}
''')
    cases.append((f'bulk{bits}',bits,16384//step,None,'1'))
    # Complete SIMD hashes on parallel messages. Pack the sixteen initial
    # words and state before timing, allowing the most favorable data layout.
    for width,guard in [(16,'defined(__aarch64__)'),(32,'defined(__AVX2__)'),(64,'defined(__AVX512F__)')]:
        lanes=width//(w//8); name=f'vec{bits}_{lanes}'; vt=name+'_t'
        print(f'#if {guard}\ntypedef {typ} {vt} __attribute__((vector_size({width})));')
        print(f'static {vt} {name}_input[16], {name}_state[8];')
        print(f'static void {name}_pack(void) {{ for(int l=0;l<{lanes};l++) {{')
        print(f'for(int j=0;j<8;j++) {name}_state[j][l]=s{bits}[l][j];')
        print(f'for(int j=0;j<16;j++) {{ {typ} t; memcpy(&t,input[l]+sizeof(t)*j,sizeof(t)); {name}_input[j][l]=__builtin_bswap{w}(t); }} }} }}')
        print(f'static NOINLINE void {name}(void) {{ {vt} W[16]; memcpy(W,{name}_input,sizeof(W));')
        print(vt+' '+','.join(f'{v}={name}_state[{i}]' for i,v in enumerate('abcdefgh'))+';')
        rot=lambda v,n:f'(({v}>>{n})|({v}<<{w-n}))'
        rr=(7,18,3,17,19,10,6,11,25,2,13,22) if bits==256 else (1,8,7,19,61,6,14,18,41,28,34,39)
        for i in range(rounds):
            j=i%16
            print('{')
            if i>=16:
                print(f'{vt} x=W[{(j+1)%16}], y=W[{(j+14)%16}];')
                print(f'W[{j}]+=({rot("x",rr[0])}^{rot("x",rr[1])}^(x>>{rr[2]})) + W[{(j+9)%16}] + ({rot("y",rr[3])}^{rot("y",rr[4])}^(y>>{rr[5]}));')
            print(f'{vt} t1=h+({rot("e",rr[6])}^{rot("e",rr[7])}^{rot("e",rr[8])})+(g^(e&(f^g)))+k{bits}[{i}]+W[{j}];')
            print(f'{vt} t2=({rot("a",rr[9])}^{rot("a",rr[10])}^{rot("a",rr[11])})+((a&b)^(c&(a^b)));')
            print('h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2; }')
        print(' '.join(f'{name}_state[{i}]+={v};' for i,v in enumerate('abcdefgh'))+'}')
        print(f'static void {name}_check(void) {{ {name}_pack(); {name}(); for(int l=0;l<{lanes};l++) for(int j=0;j<8;j++) s{bits}[l][j]={name}_state[j][l]; check{bits}({lanes}); }}\n#endif')
        cases.append((name,bits,lanes,name+'_check',guard))

# Complete independent native SHA-256 compressions, including the message schedule.
for arch,guard in [('arm','defined(__ARM_FEATURE_SHA2)'),('x86','defined(__SHA__)')]:
    print(f'#if {guard}')
    for lanes in (1,2,4,8):
        name=f'{arch}256_{lanes}'
        print(f'static NOINLINE void {name}(void) {{')
        for l in range(lanes):
            if arch=='arm':
                print(f'uint32x4_t a{l}=vld1q_u32(s256[{l}]), b{l}=vld1q_u32(s256[{l}]+4), sa{l}=a{l}, sb{l}=b{l};')
            else:
                print(f'__m128i x{l}=_mm_shuffle_epi32(_mm_loadu_si128((void*)s256[{l}]),0xb1), y{l}=_mm_shuffle_epi32(_mm_loadu_si128((void*)(s256[{l}]+4)),0x1b);')
                print(f'__m128i a{l}=_mm_alignr_epi8(x{l},y{l},8), b{l}=_mm_blend_epi16(y{l},x{l},0xf0), sa{l}=a{l}, sb{l}=b{l};')
            for j in range(4):
                ptr=f'input[{l}]+{16*j}'
                if arch=='arm': print(f'uint32x4_t w{l}_{j}=vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8({ptr})));')
                else: print(f'__m128i w{l}_{j}=_mm_shuffle_epi8(_mm_loadu_si128((void*)({ptr})),_mm_set_epi64x(0x0c0d0e0f08090a0b,0x0405060700010203));')
        for r in range(16):
            for l in range(lanes):
                m,n,o,p=[f'w{l}_{(r+x)%4}' for x in range(4)]
                if r>=4:
                    if arch=='arm': print(f'{m}=vsha256su1q_u32(vsha256su0q_u32({m},{n}),{o},{p});')
                    else: print(f'{m}=_mm_sha256msg2_epu32(_mm_add_epi32(_mm_sha256msg1_epu32({m},{n}),_mm_alignr_epi8({p},{o},4)),{p});')
                if arch=='arm': print(f'{{uint32x4_t old=a{l}, wk=vaddq_u32({m},vld1q_u32(k256+{r*4})); a{l}=vsha256hq_u32(old,b{l},wk); b{l}=vsha256h2q_u32(b{l},old,wk);}}')
                else: print(f'{{__m128i wk=_mm_add_epi32({m},_mm_loadu_si128((void*)(k256+{r*4}))); b{l}=_mm_sha256rnds2_epu32(b{l},a{l},wk); a{l}=_mm_sha256rnds2_epu32(a{l},b{l},_mm_shuffle_epi32(wk,0x0e));}}')
        for l in range(lanes):
            if arch=='arm': print(f'vst1q_u32(s256[{l}],vaddq_u32(a{l},sa{l})); vst1q_u32(s256[{l}]+4,vaddq_u32(b{l},sb{l}));')
            else:
                print(f'x{l}=_mm_shuffle_epi32(_mm_add_epi32(a{l},sa{l}),0x1b); y{l}=_mm_shuffle_epi32(_mm_add_epi32(b{l},sb{l}),0xb1);')
                print(f'_mm_storeu_si128((void*)s256[{l}],_mm_blend_epi16(x{l},y{l},0xf0)); _mm_storeu_si128((void*)(s256[{l}]+4),_mm_alignr_epi8(y{l},x{l},8));')
        print(f'}}\nstatic void {name}_check(void) {{ {name}(); check256({lanes}); }}')
        cases.append((name,256,lanes,name+'_check',guard))
    print('#endif')

# Two SHA-512 rounds per H/H2 pair, using the Arm backend's state layout.
guard = 'defined(__ARM_FEATURE_SHA512)'
print(f'#if {guard}')
for lanes in (1,2,4):
    name=f'arm512_{lanes}'
    print(f'static NOINLINE void {name}(void) {{')
    for l in range(lanes):
        for i,v in enumerate('abcd'):
            print(f'uint64x2_t {v}{l}=vld1q_u64(s512[{l}]+{2*i}), save{v}{l}={v}{l};')
        for j in range(8):
            print(f'uint64x2_t w{l}_{j}=vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(input[{l}]+{16*j})));')
    for r in range(40):
        for l in range(lanes):
            m=[f'w{l}_{(r+j)%8}' for j in range(8)]
            if r>=8:
                print(f'{m[0]}=vsha512su1q_u64(vsha512su0q_u64({m[0]},{m[1]}),{m[7]},vextq_u64({m[4]},{m[5]},1));')
            a,b,c,d=[f'{v}{l}' for v in 'abcd']
            print(f'{{uint64x2_t wk=vaddq_u64({m[0]},vld1q_u64(k512+{2*r}));')
            print(f'uint64x2_t t=vsha512hq_u64(vaddq_u64(vextq_u64(wk,wk,1),{d}),vextq_u64({c},{d},1),vextq_u64({b},{c},1));')
            print(f'uint64x2_t next=vsha512h2q_u64(t,{b},{a}); {d}={c}; {c}=vaddq_u64({b},t); {b}={a}; {a}=next; }}')
    for l in range(lanes):
        for i,v in enumerate('abcd'):
            print(f'vst1q_u64(s512[{l}]+{2*i},vaddq_u64({v}{l},save{v}{l}));')
    print(f'}}\nstatic void {name}_check(void) {{ {name}(); check512({lanes}); }}')
    cases.append((name,512,lanes,name+'_check',guard))
print('#endif')

# Issue enough independent round instructions to hide their latency.
for bits,guard,arch,groups in [(256,'defined(__ARM_FEATURE_SHA2)','arm',16),(512,'defined(__ARM_FEATURE_SHA512)','arm',40),(256,'defined(__SHA__)','x86',32)]:
    name=f'issue{bits}_{arch}'
    print(f'#if {guard}\nstatic NOINLINE void {name}(void) {{ __asm__ volatile(')
    body=[]
    if arch=='arm':
        ty='4s' if bits==256 else '2d'
        for j in range(8):
            body.extend([f'sha{bits}h q{2*j}, q16, v17.{ty}',f'sha{bits}h2 q{2*j+1}, q16, v17.{ty}'])
        regs=[f'"v{j}"' for j in range(18)]
    else:
        body=[f'sha256rnds2 %%xmm0, %%xmm9, %%xmm{j+1}' for j in range(8)]
        regs=[f'"xmm{j}"' for j in range(10)]
    print(f'".rept {groups}\\n"')
    for ins in body:print(f'"{ins}\\n"')
    print('".endr\\n" ::: '+','.join(regs)+'); }\n#endif')
    cases.append((name,bits,8,None,guard))
print('''
struct item {const char *name; int bits,blocks; void (*run)(void),(*check)(void);};
static struct item tests[] = {''')
for name,bits,blocks,check,guard in cases:
    print(f'#if {guard}\n{{"{name}",{bits},{blocks},{name},{check or "NULL"}}},\n#endif')
print('''};
int main(int argc, char **argv) {
  SHA256_Init(&stream256); SHA512_Init(&stream512);
  for(int l=0;l<16;l++) for(int j=0;j<128;j++) input[l][j]=l*11+j*7;
  const int n=sizeof(tests)/sizeof(tests[0]);
  for(int i=0;i<n;i++) {
    for(int l=0;l<16;l++) for(int j=0;j<8;j++) s256[l][j]=s512[l][j]=37*l+j;
    if(tests[i].check) tests[i].check();
  }
  int first=argc>1?atoi(argv[1]):0, last=argc>1?first:6;
  for(int r=first;r<=last;r++) for(int j=0;j<n;j++) {
    struct item t=tests[(j+r)%n];
    int iters=(1<<20)/t.blocks;
    double start=ns();
    for(int i=0;i<iters;i++) { __asm__ volatile("":::"memory"); t.run(); }
    printf("%s,%d,%d,%.6f\\n",t.name,t.bits,r,(ns()-start)/(iters*t.blocks));
  }
}''')
