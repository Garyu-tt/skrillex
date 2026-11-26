/* Public synthetic instruction fixtures; no game binary required. */
#define main skrillex_runtime_main
#include "../source/main.c"
#undef main
#include <assert.h>
static void instruction_fixture(void) {
 static const uint8_t program[]={
  0xb8,0x81,0x80,0x34,0x12, /* mov eax,12348081h */
  0xd0,0xc0,               /* rol al,1 */
  0x66,0xbb,0x00,0x80,     /* mov bx,8000h */
  0x66,0xc1,0xfb,0x03,     /* sar bx,3 */
  0x66,0x53,0x66,0x59,     /* push bx; pop cx */
  0x0f,0xbd,0xd0,          /* bsr edx,eax */
  0x0f,0xbc,0xd8,          /* bsf ebx,eax */
  0x66,0x81,0xf9,0x00,0xf0 /* cmp cx,f000h */
 };
 base=0x400000;size=sizeof program;image=malloc(size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,program,size);
 ip=base;memset(r,0,sizeof r);r[4]=BASESTACK+STACKSIZE-16;uint32_t initial_sp=r[4];
 steps=0;fault=0;zflag=sflag=cflag=oflag=pflag=aflag=dflag=0;
 assert(step()&&r[0]==0x12348081u);
 assert(step()&&r[0]==0x12348003u&&cflag&&oflag);
 assert(step()&&(r[3]&65535)==0x8000);
 assert(step()&&(r[3]&65535)==0xf000&&sflag);
 assert(step()&&r[4]==initial_sp-2);
 assert(step()&&r[4]==initial_sp&&(r[1]&65535)==0xf000);
 assert(step()&&r[2]==28&&!zflag);
 assert(step()&&r[3]==0&&!zflag);
 assert(step()&&zflag&&!cflag);
 assert(ip==base+size&&!fault&&steps==9);
 free(image);free(stack);image=stack=NULL;size=0;
}
static void dynamic_import_fixture(void){
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);
 fault=0;import_count=api_calls=last_error=0;kernel_refs=1;
 uint32_t sp=BASESTACK+STACKSIZE-64;r[4]=sp;
 memcpy(image,"KERNEL32.DLL",13);memcpy(image+32,"GetTickCount",13);memcpy(image+64,"UnknownExport",14);
 uint32_t load=kernel_export("LoadLibraryA"),proc=kernel_export("GetProcAddress"),release=kernel_export("FreeLibrary");
 assert(load&&proc&&release&&load!=proc);
 write32(sp,base);assert(api_call(load,1)==1&&r[0]==KERNEL32_HANDLE&&kernel_refs==2&&r[4]==sp+4);
 r[4]=sp;write32(sp,KERNEL32_HANDLE);write32(sp+4,base+32);
 assert(api_call(proc,1)==1&&r[0]==kernel_export("GetTickCount")&&r[4]==sp+8);
 uint32_t tick=r[0];unsigned count=import_count;assert(kernel_export("GetTickCount")==tick&&import_count==count);
 assert(!kernel_export("gettickcount"));
 r[4]=sp;write32(sp,KERNEL32_HANDLE);write32(sp+4,base+64);
 assert(api_call(proc,1)==1&&!r[0]&&last_error==127&&import_count==count);
 r[4]=sp;write32(sp,base+64);
 assert(api_call(load,1)==1&&!r[0]&&last_error==126);
 r[4]=sp;write32(sp,0x400123);write32(sp+4,KERNEL32_HANDLE);
 assert(api_call(release,0)==1&&r[0]==1&&kernel_refs==1&&ip==0x400123&&r[4]==sp+8);
 free(image);free(stack);image=stack=NULL;size=0;
}
int main(void){assert(test());dynamic_import_fixture();instruction_fixture();puts("Synthetic x86 instruction and dynamic import fixtures: PASS");return 0;}
