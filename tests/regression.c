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
int main(void){assert(test());instruction_fixture();puts("Synthetic x86 instruction fixture: PASS (9 instructions)");return 0;}
