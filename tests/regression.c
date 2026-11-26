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
static void xadd_fixture(void){
 static const uint8_t code[]={
  0x0f,0xc1,0xd8, /* xadd eax, ebx */
  0x0f,0xc1,0xc0, /* xadd eax, eax */
  0x0f,0xc0,0xe0, /* xadd al, ah */
  0x66,0x0f,0xc1,0xd8, /* xadd ax, bx */
  0xf0,0x0f,0xc1,0x0d,0x00,0x01,0x40,0x00, /* lock xadd [400100h], ecx */
  0xf0,0x0f,0xc1,0xc0 /* invalid register LOCK */
 };
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,code,sizeof code);
 fault=0;ip=base;steps=0;memset(r,0,sizeof r);r[0]=0xffffffff;r[3]=1;
 assert(step()&&r[0]==0&&r[3]==0xffffffff&&cflag&&zflag);
 r[0]=0x40000000;assert(step()&&r[0]==0x80000000&&oflag&&!cflag&&sflag);
 r[0]=0xabcd017f;assert(step()&&r[0]==0xabcd7f80&&oflag&&sflag&&!cflag);
 r[0]=0x1234ffff;r[3]=0x56780001;assert(step()&&r[0]==0x12340000&&r[3]==0x5678ffff&&cflag&&zflag);
 write32(base+256,10);r[1]=3;assert(step()&&read32(base+256)==13&&r[1]==10&&!cflag&&!zflag);
 uint32_t prev=r[0];assert(!step()&&r[0]==prev&&!fault&&steps==5);
 free(image);free(stack);image=stack=NULL;size=0;steps=0;
}
static void cmpxchg_fixture(void){
 static const uint8_t code[]={
  0x0f,0xb1,0xd9, /* cmpxchg ecx, ebx: match */
  0x0f,0xb1,0xd9, /* mismatch */
  0x0f,0xb0,0xe1, /* cmpxchg cl, ah */
  0x66,0x0f,0xb1,0xd9, /* cmpxchg cx, bx */
  0xf0,0x0f,0xb1,0x1d,0x00,0x01,0x40,0x00, /* lock cmpxchg memory, ebx */
  0xf0,0x0f,0xb1,0xd9 /* invalid lock register */
 };
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,code,sizeof code);
 fault=0;ip=base;steps=0;memset(r,0,sizeof r);r[0]=7;r[1]=7;r[3]=9;
 assert(step()&&r[0]==7&&r[1]==9&&r[3]==9&&zflag&&!cflag);
 assert(step()&&r[0]==9&&r[1]==9&&!zflag&&cflag);
 r[0]=0x12348001;r[1]=0x87654301;
 assert(step()&&r[0]==0x12348001&&r[1]==0x87654380&&zflag);
 r[0]=0xabcd8000;r[1]=0x12340001;r[3]=0x567800ff;
 assert(step()&&r[0]==0xabcd0001&&r[1]==0x12340001&&!zflag&&oflag);
 write32(base+256,11);r[0]=11;r[3]=42;
 assert(step()&&read32(base+256)==42&&r[0]==11&&zflag);
 uint32_t old=r[1];assert(!step()&&r[1]==old&&!fault&&steps==5);
 free(image);free(stack);image=stack=NULL;size=0;steps=0;
}
static void muldiv_fixture(void){
 static const uint8_t code[]={
  0xf6,0xe3, /* mul bl */
  0xf6,0xeb, /* imul bl */
  0xf6,0xf3, /* div bl */
  0xf6,0xfb, /* idiv bl */
  0x66,0xf7,0xe3, /* mul bx */
  0x66,0xf7,0xeb, /* imul bx */
  0x66,0xf7,0xf3, /* div bx */
  0x66,0xf7,0xfb, /* idiv bx */
  0x66,0x0f,0xaf,0xc3, /* imul ax,bx */
  0x66,0x69,0xcb,0x00,0x01, /* imul cx,bx,256 */
  0x66,0x6b,0xcb,0xfe, /* imul cx,bx,-2 */
  0xf6,0xf3, /* divide by zero */
  0xf6,0xf3, /* quotient overflow */
  0x66,0xf7,0xfb /* signed overflow */
 };
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,code,sizeof code);
 fault=0;ip=base;steps=0;memset(r,0,sizeof r);
 r[0]=0xabcd00ff;r[3]=2;assert(step()&&r[0]==0xabcd01fe&&cflag&&oflag);
 r[0]=0xabcd00fe;r[3]=3;assert(step()&&r[0]==0xabcdfffa&&!cflag&&!oflag);
 r[0]=0xabcd0101;r[3]=3;cflag=1;zflag=1;assert(step()&&r[0]==0xabcd0255&&cflag&&zflag);
 r[0]=0xabcdfff9;r[3]=3;assert(step()&&r[0]==0xabcdfffe);
 r[0]=0x1234ffff;r[2]=0x56780000;r[3]=2;assert(step()&&r[0]==0x1234fffe&&r[2]==0x56780001&&cflag&&oflag);
 r[0]=0x1234fffe;r[3]=3;assert(step()&&r[0]==0x1234fffa&&r[2]==0x5678ffff&&!cflag&&!oflag);
 r[0]=0x12340005;r[2]=0x56780001;r[3]=3;assert(step()&&r[0]==0x12345557&&r[2]==0x56780000);
 r[0]=0x1234fff9;r[2]=0x5678ffff;r[3]=3;assert(step()&&r[0]==0x1234fffe&&r[2]==0x5678ffff);
 r[0]=0x12344000;r[3]=3;assert(step()&&r[0]==0x1234c000&&cflag&&oflag);
 r[1]=0xaabb0000;r[3]=128;assert(step()&&r[1]==0xaabb8000&&cflag&&oflag);
 assert(step()&&r[1]==0xaabbff00&&!cflag&&!oflag);
 r[0]=0x12340100;r[3]=0;assert(!step()&&r[0]==0x12340100&&!fault&&steps==11);
 r[3]=1;assert(!step()&&r[0]==0x12340100&&!fault&&steps==11);
 r[0]=0x12340000;r[2]=0x56788000;r[3]=65535;
 assert(!step()&&r[0]==0x12340000&&r[2]==0x56788000&&!fault&&steps==11);
 free(image);free(stack);image=stack=NULL;size=0;steps=0;
}
static void double_shift_fixture(void){
 static const uint8_t code[]={
  0x0f,0xa4,0xd8,4, /* shld eax,ebx,4 */
  0x0f,0xad,0xd8, /* shrd eax,ebx,cl */
  0x66,0x0f,0xa4,0xd8,16, /* shld ax,bx,16 */
  0x66,0x0f,0xac,0xd8,1, /* shrd ax,bx,1 */
  0x0f,0xa4,0xd8,32, /* masked zero */
  0x66,0x0f,0xbc,0xc3, /* bsf ax,bx */
  0x66,0x0f,0xbd,0xc3, /* bsr ax,bx */
  0x66,0x0f,0xab,0x0d,0x04,0x01,0x40,0x00, /* bts word [400104h],cx */
  0x66,0xf0,0x0f,0xb3,0x0d,0x04,0x01,0x40,0x00, /* lock btr word [400104h],cx */
 };
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,code,sizeof code);
 fault=0;ip=base;steps=0;memset(r,0,sizeof r);
 r[0]=0x81234567;r[3]=0xabcdef01;
 assert(step()&&r[0]==0x1234567a&&!cflag&&!zflag);
 r[0]=0x12345678;r[3]=0xf0000001;r[1]=4;
 assert(step()&&r[0]==0x11234567&&cflag);
 r[0]=0xabcd8001;r[3]=0x12345678;
 assert(step()&&r[0]==0xabcd5678&&cflag);
 r[0]=0xabcd0001;r[3]=0x12340001;
 assert(step()&&r[0]==0xabcd8000&&cflag&&oflag&&sflag);
 r[0]=0x12345678;cflag=zflag=oflag=pflag=aflag=sflag=1;
 assert(step()&&r[0]==0x12345678&&cflag&&zflag&&oflag&&pflag&&aflag&&sflag);
 r[0]=0xabcd9999;r[3]=0x12348010;assert(step()&&r[0]==0xabcd0004&&!zflag);
 assert(step()&&r[0]==0xabcd000f&&!zflag);
 r[1]=0xffff;write32(base+0x100,0);write32(base+0x104,0);
 assert(step()&&read32(base+0x100)==0x80000000&&!cflag);
 assert(step()&&read32(base+0x100)==0&&cflag);
 assert(steps==9&&!fault);
 free(image);free(stack);image=stack=NULL;size=0;steps=0;
}
static void cmpxchg8b_fixture(void){
 static const uint8_t code[]={
  0x0f,0xc7,0x0d,0x00,0x01,0x40,0x00,
  0xf0,0x0f,0xc7,0x0d,0x00,0x01,0x40,0x00,
  0x0f,0xc7,0xc9
 };
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,code,sizeof code);
 fault=0;ip=base;steps=0;memset(r,0,sizeof r);
 write32(base+256,0x89abcdef);write32(base+260,0x12345678);
 r[0]=0x89abcdef;r[2]=0x12345678;r[3]=0xaabbccdd;r[1]=0x55667788;cflag=sflag=oflag=pflag=aflag=1;
 assert(step()&&zflag&&read32(base+256)==r[3]&&read32(base+260)==r[1]);
 assert(step()&&!zflag&&r[0]==0xaabbccdd&&r[2]==0x55667788);
 assert(cflag&&sflag&&oflag&&pflag&&aflag);
 assert(!step()&&!fault&&steps==2);
 free(image);free(stack);image=stack=NULL;size=0;steps=0;
}
static void stack_forms_fixture(void){
 static const uint8_t code[]={
  0x8f,0xc3, /* pop ebx */
  0x8f,0x04,0x24, /* pop [esp] */
  0x66,0x8f,0xc1, /* pop cx */
  0x66,0xff,0xf1, /* push cx */
  0x8f,0xc4, /* pop esp */
  0x8f,0xc8, /* invalid group */
  0x8f,0x05,0x00,0x00,0x00,0x00 /* invalid destination */
 };
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,code,sizeof code);
 fault=0;ip=base;steps=0;memset(r,0,sizeof r);
 uint32_t sp=BASESTACK+STACKSIZE-64;r[4]=sp;
 write32(sp,0x11223344);write32(sp+4,0xaabbccdd);write32(sp+8,0x55667788);
 cflag=zflag=sflag=oflag=pflag=aflag=dflag=1;
 assert(step()&&r[3]==0x11223344&&r[4]==sp+4);
 assert(step()&&r[4]==sp+8&&read32(sp+8)==0xaabbccdd);
 r[1]=0x12340000;assert(step()&&r[1]==0x1234ccdd&&r[4]==sp+10);
 assert(step()&&r[4]==sp+8&&get16((Operand){0,0,sp+8})==0xccdd);
 write32(sp+8,sp+24);assert(step()&&r[4]==sp+24);
 assert(cflag&&zflag&&sflag&&oflag&&pflag&&aflag&&dflag);
 assert(!step()&&r[4]==sp+24&&!fault&&steps==5);
 assert(!step()&&r[4]==sp+24&&fault&&steps==5);
 free(image);free(stack);image=stack=NULL;size=0;steps=fault=0;
}
static void tsc_fixture(void){
 static const uint8_t program[]={0x0f,0x31,0x0f,0x31,0x0f,0xa2};
 base=0x400000;size=512;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);memcpy(image,program,sizeof program);
 fault=0;ip=base;memset(r,0,sizeof r);r[4]=BASESTACK+STACKSIZE-64;
 steps=429496729u;cflag=zflag=sflag=oflag=pflag=aflag=dflag=1;
 assert(step()&&r[0]==4294967290u&&r[2]==0);
 assert(step()&&r[0]==4&&r[2]==1);
 assert(cflag&&zflag&&sflag&&oflag&&pflag&&aflag&&dflag);
 r[0]=1;assert(step()&&(r[2]&16));
 import_count=api_calls=0;uint32_t sp=r[4];write32(sp,base+64);
 assert(api_call(kernel_export("QueryPerformanceCounter"),1)==1&&r[0]==1);
 assert(((uint64_t)read32(base+68)<<32|read32(base+64))==guest_ticks());
 r[4]=sp;write32(sp,base+64);
 assert(api_call(kernel_export("QueryPerformanceFrequency"),1)==1&&read32(base+64)==1000000&&read32(base+68)==0);
 free(image);free(stack);image=stack=NULL;size=0;steps=0;
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
static uint32_t user_fixture_call(const char*name,const uint32_t*args,unsigned n){
 uint32_t sp=BASESTACK+STACKSIZE-256;r[4]=sp;
 for(unsigned i=0;i<n;i++)write32(sp+4*i,args[i]);
 uint32_t token=user_export(name);assert(token&&api_call(token,1)==1&&!fault&&r[4]==sp+4*n);
 return r[0];
}
static void user_window_fixture(void){
 base=0x400000;size=1024;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);
 fault=0;import_count=api_calls=steps=0;message_count=window_serial=callback_depth=0;
 memset(classes,0,sizeof classes);memset(windows,0,sizeof windows);
 memset(r,0,sizeof r);ip=base+0x300;
 /* mov eax,[esp+8]; mov [400200h],eax; ret 16 */
 static const uint8_t proc[]={0x8b,0x44,0x24,0x08,0xa3,0x00,0x02,0x40,0x00,0xc2,0x10,0x00};
 memcpy(image+0x20,proc,sizeof proc);memcpy(image+0x180,"FixtureClass",13);
 write32(base+0x104,base+0x20);write32(base+0x110,base);write32(base+0x124,base+0x180);
 uint32_t atom=user_fixture_call("RegisterClassA",(uint32_t[]){base+0x100},1);assert(atom==1);
 assert(!user_fixture_call("RegisterClassA",(uint32_t[]){base+0x100},1)&&last_error==1410);
 uint32_t hwnd=user_fixture_call("CreateWindowExA",(uint32_t[]){0,atom,0,0,10,20,640,480,0,0,base,0},12);
 assert(hwnd&&window_find(hwnd)&&steps==6&&read32(base+0x200)==1&&ip==base+0x300);
 assert(user_fixture_call("GetClientRect",(uint32_t[]){hwnd,base+0x240},2)==1);
 assert(read32(base+0x240)==0&&read32(base+0x248)==640&&read32(base+0x24c)==480);
 assert(user_fixture_call("PostMessageA",(uint32_t[]){hwnd,0x401,7,9},4)==1);
 assert(user_fixture_call("PeekMessageA",(uint32_t[]){base+0x260,hwnd,0,0,0},5)==1&&message_count==1);
 assert(user_fixture_call("PeekMessageA",(uint32_t[]){base+0x260,hwnd,0,0,1},5)==1&&message_count==0);
 assert(read32(base+0x264)==0x401&&read32(base+0x268)==7&&read32(base+0x26c)==9);
 assert(user_fixture_call("DispatchMessageA",(uint32_t[]){base+0x260},1)==0x401&&read32(base+0x200)==0x401&&steps==9);
 assert(user_fixture_call("IsWindow",(uint32_t[]){hwnd},1)==1);
 assert(user_fixture_call("IsWindow",(uint32_t[]){0xdead},1)==0);
 user_fixture_call("PostQuitMessage",(uint32_t[]){42},1);
 assert(user_fixture_call("PeekMessageA",(uint32_t[]){base+0x260,hwnd,0,0,1},5)==1&&read32(base+0x264)==0x12&&read32(base+0x268)==42);
 /* Reject WM_NCCREATE by returning zero, with no live window leaked. */
 static const uint8_t reject[]={0x31,0xc0,0xc2,0x10,0x00};memcpy(image+0x20,reject,sizeof reject);
 assert(!user_fixture_call("CreateWindowExA",(uint32_t[]){0,atom,0,0,0,0,320,240,0,0,base,0},12));
 assert(!window_find(0x20002u)&&window_find(hwnd)&&!callback_depth);
 free(image);free(stack);image=stack=NULL;size=0;
}
static uint32_t kernel_fixture_call(const char*name,const uint32_t*args,unsigned n){
 uint32_t sp=BASESTACK+STACKSIZE-256;r[4]=sp;
 for(unsigned i=0;i<n;i++)write32(sp+4*i,args[i]);
 uint32_t token=kernel_export(name);assert(token&&api_call(token,1)==1&&!fault&&r[4]==sp+4*n);return r[0];
}
static void file_fixture(void){
 char path[512];
 assert(resource_path("models\\gta3.img",path,sizeof path)&&!strcmp(path,"models/gta3.img"));
 assert(resource_path("C:\\games\\Grand Theft Auto San Andreas\\data\\gta.dat",path,sizeof path)&&!strcmp(path,"data/gta.dat"));
 const char*bad[]={"../file","a/../file","/file","D:/file","C:foo","a//b","a/","a/CON.txt","NUL","COM1","LPT9.txt","a/.. ","a/b:stream","a/."};
 for(unsigned i=0;i<sizeof bad/sizeof bad[0];i++)assert(!resource_path(bad[i],path,sizeof path));
 assert(!resource_path("long",path,3));
 base=0x400000;size=1024;image=calloc(1,size);stack=calloc(1,STACKSIZE);assert(image&&stack);
 fault=0;import_count=api_calls=0;memset(r,0,sizeof r);
 FILE*f=tmpfile();assert(f);assert(fwrite("abcdef",1,6,f)==6);uint32_t h=file_adopt(f);assert(h!=UINT32_MAX);
 assert(kernel_fixture_call("GetFileType",(uint32_t[]){h},1)==1);
 assert(kernel_fixture_call("GetFileSizeEx",(uint32_t[]){h,base+0x100},2)==1&&read32(base+0x100)==6&&read32(base+0x104)==0);
 assert(kernel_fixture_call("ReadFile",(uint32_t[]){h,base+0x200,4,base+0x110,0},5)==1&&read32(base+0x110)==4&&!memcmp(image+0x200,"abcd",4));
 assert(kernel_fixture_call("SetFilePointerEx",(uint32_t[]){h,0xfffffffe,UINT32_MAX,base+0x120,2},5)==1&&read32(base+0x120)==4);
 assert(kernel_fixture_call("ReadFile",(uint32_t[]){h,base+0x200,4,base+0x110,0},5)==1&&read32(base+0x110)==2&&!memcmp(image+0x200,"ef",2));
 assert(kernel_fixture_call("ReadFile",(uint32_t[]){h,base+0x200,4,base+0x110,0},5)==1&&!read32(base+0x110));
 assert(kernel_fixture_call("SetFilePointer",(uint32_t[]){h,UINT32_MAX,0,0},4)==UINT32_MAX&&last_error==131);
 assert(!kernel_fixture_call("WriteFile",(uint32_t[]){h,base+0x200,2,base+0x110,0},5)&&last_error==5);
 assert(kernel_fixture_call("CloseHandle",(uint32_t[]){h},1)==1&&!file_find(h));
 assert(!kernel_fixture_call("CloseHandle",(uint32_t[]){h},1)&&last_error==6);
 memcpy(image,"../file",8);
 assert(kernel_fixture_call("CreateFileA",(uint32_t[]){base,0x80000000,1,0,3,0,0},7)==UINT32_MAX&&last_error==123);
 memcpy(image,"valid.dat",10);
 assert(kernel_fixture_call("CreateFileA",(uint32_t[]){base,0x40000000,1,0,2,0,0},7)==UINT32_MAX&&last_error==5);
 assert(kernel_fixture_call("CreateFileA",(uint32_t[]){base,0x80000000,1,0,3,0,0},7)==UINT32_MAX&&last_error==2);
 close_guest_files();free(image);free(stack);image=stack=NULL;size=0;
}
static uint32_t d3d_fixture_call(uint32_t token,const uint32_t*args,unsigned n){
 uint32_t sp=BASESTACK+STACKSIZE-256;r[4]=sp;for(unsigned i=0;i<n;i++)write32(sp+4*i,args[i]);
 assert(token&&api_call(token,1)==1&&!fault&&r[4]==sp+4*n);return r[0];
}
static uint32_t com_token(uint32_t obj,unsigned slot){return read32(read32(obj)+4*slot);}
static void d3d_fixture(void){
 base=0x400000;size=1024;image=calloc(1,size);stack=calloc(1,STACKSIZE);heap=calloc(1,HEAPSIZE);assert(image&&stack&&heap);
 fault=0;import_count=api_calls=0;heapnext=4096;memset(r,0,sizeof r);memset(windows,0,sizeof windows);
 windows[0]=(GuestWindow){0x20001,base,0,0,4,3,1};
 uint32_t create=d3d_token("Direct3DCreate9");
 assert(!d3d_fixture_call(create,(uint32_t[]){31},1));
 uint32_t root=d3d_fixture_call(create,(uint32_t[]){32},1);assert(root&&d3d_root.refs==1);
 assert(d3d_fixture_call(com_token(root,4),(uint32_t[]){root},1)==1);
 uint32_t pp=base+0x100,out=base+0x180;
 write32(pp,4);write32(pp+4,3);write32(pp+8,22);write32(pp+12,1);write32(pp+24,1);write32(pp+28,0x20001);write32(pp+32,1);
 assert(d3d_fixture_call(com_token(root,16),(uint32_t[]){root,0,1,0x20001,0x20,pp,out},7)==0);
 uint32_t dev=read32(out);assert(dev&&color_buffer&&d3d_width==4&&d3d_height==3&&d3d_root.refs==2);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff123456,0x3f800000,0},7)==0);
 for(unsigned i=0;i<12;i++)assert(color_buffer[i]==0xff123456);
 assert(d3d_fixture_call(com_token(dev,17),(uint32_t[]){dev,0,0,0,0},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,17),(uint32_t[]){dev,0,0,0,0},5)==0&&d3d_frames==1);
 assert(d3d_hash==0x91193335u);
 /* Actual guest vertex data: a triangle covering six pixels of a 4x3 target. */
 uint32_t vertices=base+0x200;
 const float coords[3][4]={{0,0,0,1},{3,0,0,1},{0,3,0,1}};
 for(unsigned i=0;i<3;i++){memcpy(image+0x200+20*i,coords[i],16);write32(vertices+20*i+16,0xff00ff00);}
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,89),(uint32_t[]){dev,0x44},2)==0);
 assert(d3d_fixture_call(com_token(dev,90),(uint32_t[]){dev,base+0x190},2)==0&&read32(base+0x190)==0x44);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==0&&d3d_draws==1);
 unsigned green=0;for(unsigned y=0;y<3;y++)for(unsigned x=0;x<4;x++){
  uint32_t expected=x+y<3?0xff00ff00:0xff123456;
  assert(color_buffer[y*4+x]==expected);green+=expected==0xff00ff00;
 }assert(green==6);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,16},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,17),(uint32_t[]){dev,0,0,0,0},5)==0&&d3d_frames==2&&d3d_hash==0x3d35d94du);

 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,2,0,0,0},7)==D3D_INVALID);
 /* Recreate with a D16 buffer, then render overlapping near/far triangles. */
 assert(d3d_fixture_call(com_token(dev,2),(uint32_t[]){dev},1)==0&&!color_buffer);
 write32(pp+36,1);write32(pp+40,80);
 assert(d3d_fixture_call(com_token(root,16),(uint32_t[]){root,0,1,0x20001,0x20,pp,out},7)==0);
 dev=read32(out);assert(depth_buffer&&depth_enable&&depth_write&&depth_func==4);
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,3,0xff000000,0x3f800000,0},7)==0);
 assert(d3d_fixture_call(com_token(dev,89),(uint32_t[]){dev,0x44},2)==0);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 for(unsigned i=0;i<3;i++){write32(vertices+20*i+8,0x3e800000);write32(vertices+20*i+16,0xff0000ff);}
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==0);
 assert(color_buffer[0]==0xff0000ff&&depth_buffer[0]==16384);
 for(unsigned i=0;i<3;i++){write32(vertices+20*i+8,0x3f400000);write32(vertices+20*i+16,0xffff0000);}
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==0);
 assert(color_buffer[0]==0xff0000ff&&depth_buffer[0]==16384);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,23,5},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,14,0},3)==0);
 assert(d3d_fixture_call(com_token(dev,58),(uint32_t[]){dev,23,base+0x190},3)==0&&read32(base+0x190)==5);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==0);
 assert(color_buffer[0]==0xffff0000&&depth_buffer[0]==16384);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,23,9},3)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,2,0,0x3f000000,0},7)==0);
 assert(depth_buffer[0]==32768&&color_buffer[0]==0xffff0000);
 /* Vertex buffer: guest Lock writes, bound stream, range checks, refcounts. */
 uint32_t vbout=base+0x1a0,locked=base+0x1a4;
 assert(d3d_fixture_call(com_token(dev,26),(uint32_t[]){dev,60,8,0x44,0,vbout,0},7)==0);
 uint32_t vb=read32(vbout);assert(vb&&vb_find(vb));
 assert(d3d_fixture_call(com_token(vb,11),(uint32_t[]){vb,0,0,locked,0},5)==0);
 uint32_t data=read32(locked);assert(data&&vb_find(vb)->locked);
 memcpy(ptr(data,60),ptr(vertices,60),60);
 assert(d3d_fixture_call(com_token(vb,11),(uint32_t[]){vb,0,60,locked,0},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,100),(uint32_t[]){dev,0,vb,0,20},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(vb,12),(uint32_t[]){vb},1)==0);
 assert(d3d_fixture_call(com_token(vb,13),(uint32_t[]){vb,base+0x1b0},2)==0&&read32(base+0x1c0)==60&&read32(base+0x1c4)==0x44);
 assert(d3d_fixture_call(com_token(dev,100),(uint32_t[]){dev,0,vb,0,20},5)==0&&vb_find(vb)->com.refs==2);
 assert(d3d_fixture_call(com_token(dev,101),(uint32_t[]){dev,0,base+0x1d0,base+0x1d4,base+0x1d8},5)==0);
 assert(read32(base+0x1d0)==vb&&read32(base+0x1d4)==0&&read32(base+0x1d8)==20&&vb_find(vb)->com.refs==3);
 assert(d3d_fixture_call(com_token(vb,2),(uint32_t[]){vb},1)==2);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,7,0},3)==0);
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff000000,0,0},7)==0);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,81),(uint32_t[]){dev,4,1,1},4)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,81),(uint32_t[]){dev,4,0,1},4)==0);
 assert(color_buffer[0]==0xffff0000&&color_buffer[3]==0xff000000);
 /* Index buffer and indexed draw use the previously bound vertex stream. */
 for(unsigned fmt=101;fmt<=102;fmt++){
  unsigned iw=fmt==101?2:4;uint32_t ibout=base+0x1e0;
  assert(d3d_fixture_call(com_token(dev,27),(uint32_t[]){dev,3*iw,8,fmt,0,ibout,0},7)==0);
  uint32_t ib=read32(ibout);assert(ib&&ib_find(ib));
  assert(d3d_fixture_call(com_token(ib,11),(uint32_t[]){ib,0,0,locked,0},5)==0);
  uint8_t*idx=ptr(read32(locked),3*iw);assert(idx);
  memset(idx,0,3*iw);idx[0]=1;idx[iw]=2;idx[2*iw]=3;
  assert(d3d_fixture_call(com_token(dev,104),(uint32_t[]){dev,ib},2)==D3D_INVALID);
  assert(d3d_fixture_call(com_token(ib,12),(uint32_t[]){ib},1)==0);
  assert(d3d_fixture_call(com_token(ib,13),(uint32_t[]){ib,base+0x1b0},2)==0&&read32(base+0x1b0)==fmt&&read32(base+0x1c0)==3*iw);
  assert(d3d_fixture_call(com_token(dev,104),(uint32_t[]){dev,ib},2)==0);
  assert(d3d_fixture_call(com_token(dev,105),(uint32_t[]){dev,ibout},2)==0&&read32(ibout)==ib&&ib_find(ib)->com.refs==3);
  assert(d3d_fixture_call(com_token(ib,2),(uint32_t[]){ib},1)==2);
  assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff000000,0,0},7)==0);
  assert(d3d_fixture_call(com_token(dev,82),(uint32_t[]){dev,4,0,1,3,0,1},7)==D3D_INVALID);
  assert(d3d_fixture_call(com_token(dev,82),(uint32_t[]){dev,4,UINT32_MAX,1,2,0,1},7)==D3D_INVALID);
  assert(d3d_fixture_call(com_token(dev,82),(uint32_t[]){dev,4,UINT32_MAX,1,3,1,1},7)==D3D_INVALID);
  assert(color_buffer[0]==0xff000000);
  assert(d3d_fixture_call(com_token(dev,82),(uint32_t[]){dev,4,UINT32_MAX,1,3,0,1},7)==0);
  assert(color_buffer[0]==0xffff0000&&color_buffer[3]==0xff000000);
  assert(d3d_fixture_call(com_token(ib,2),(uint32_t[]){ib},1)==1);
  assert(d3d_fixture_call(com_token(dev,104),(uint32_t[]){dev,0},2)==0&&!ib_find(ib)&&!index_stream);
 }
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(vb,2),(uint32_t[]){vb},1)==1);
 assert(d3d_fixture_call(com_token(dev,100),(uint32_t[]){dev,0,0,0,0},5)==0&&!vb_find(vb)&&!stream0);
 /* Textures: guest writes into a 2x2 surface, then draws a modulated triangle. */
 uint32_t texout=base+0x1e0;
 assert(d3d_fixture_call(com_token(dev,23),(uint32_t[]){dev,2,2,1,0,21,0,texout,0},9)==0);
 uint32_t tex=read32(texout);assert(tex&&texture_find(tex));
 assert(d3d_fixture_call(com_token(tex,13),(uint32_t[]){tex},1)==1);
 assert(d3d_fixture_call(com_token(tex,17),(uint32_t[]){tex,0,base+0x1b0},3)==0&&read32(base+0x1c8)==2&&read32(base+0x1cc)==2);
 assert(d3d_fixture_call(com_token(tex,19),(uint32_t[]){tex,0,base+0x1b0,0,0},5)==0&&read32(base+0x1b0)==8);
 uint32_t pixels=read32(base+0x1b4);
 write32(pixels,0xffff0000);write32(pixels+4,0xff00ff00);write32(pixels+8,0xff0000ff);write32(pixels+12,0xffffffff);
 assert(d3d_fixture_call(com_token(dev,65),(uint32_t[]){dev,0,tex},3)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(tex,20),(uint32_t[]){tex,0},2)==0);
 assert(d3d_fixture_call(com_token(dev,65),(uint32_t[]){dev,0,tex},3)==0);
 assert(d3d_fixture_call(com_token(dev,64),(uint32_t[]){dev,0,texout},3)==0&&read32(texout)==tex&&texture_find(tex)->com.refs==3);
 assert(d3d_fixture_call(com_token(tex,2),(uint32_t[]){tex},1)==2);
 assert(texture_sample(16384,16384)==0xffff0000);
 assert(texture_sample(49152,16384)==0xff00ff00);
 assert(texture_sample(-16384,16384)==0xff00ff00);
 assert(d3d_fixture_call(com_token(dev,69),(uint32_t[]){dev,0,1,3},4)==0);
 assert(texture_sample(-16384,16384)==0xffff0000);
 assert(d3d_fixture_call(com_token(dev,69),(uint32_t[]){dev,0,5,2},4)==0);
 assert(d3d_fixture_call(com_token(dev,69),(uint32_t[]){dev,0,6,2},4)==0);
 assert(texture_sample(32768,32768)==0xff808080);
 assert(d3d_fixture_call(com_token(dev,68),(uint32_t[]){dev,0,6,texout},4)==0&&read32(texout)==2);
 assert(d3d_fixture_call(com_token(dev,89),(uint32_t[]){dev,0x144},2)==0);
 for(unsigned i=0;i<3;i++){memcpy(image+0x200+28*i,coords[i],16);write32(vertices+28*i+16,0xffffffff);write32(vertices+28*i+20,0x3f000000);write32(vertices+28*i+24,0x3f000000);}
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff000000,0,0},7)==0);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,28},5)==0);
 assert(color_buffer[0]==0xff808080&&color_buffer[3]==0xff000000);
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(tex,2),(uint32_t[]){tex},1)==1);
 assert(d3d_fixture_call(com_token(dev,65),(uint32_t[]){dev,0,0},3)==0&&!texture_find(tex)&&!texture0);
 /* Compressed texture blocks stay in guest memory. */
 assert(texture_size(1024,1024,FMT_DXT1)==524288);
 assert(texture_size(1024,1024,FMT_DXT5)==1048576);
 assert(texture_pitch(5,FMT_DXT1)==16&&texture_size(5,7,FMT_DXT1)==32);
 const uint32_t formats[]={FMT_DXT1,FMT_DXT3,FMT_DXT5};
 for(unsigned fi=0;fi<3;fi++){
  uint32_t fmt=formats[fi],block=texture_block_bytes(fmt);
  assert(d3d_fixture_call(com_token(dev,23),(uint32_t[]){dev,5,7,1,0,fmt,0,texout,0},9)==0);
  uint32_t obj=read32(texout);GuestTexture*t=texture_find(obj);assert(t);
  assert(find_block(HEAPBASE,t->data)->requested==block*4);
  assert(d3d_fixture_call(com_token(obj,19),(uint32_t[]){obj,0,base+0x1b0,0,0},5)==0&&read32(base+0x1b0)==block*2);
  uint8_t*data=ptr(read32(base+0x1b4),block*4);assert(data);
  for(unsigned k=0;k<4;k++){
   uint8_t*b=data+k*block;uint8_t*c=b+(fi?8:0);
   c[0]=0;c[1]=0xf8;c[2]=0xe0;c[3]=7; /* red, green */
   c[4]=0xe4; /* selectors 0,1,2,3 in first row */
   if(fi==1)b[0]=0xf1;
   if(fi==2){b[0]=200;b[1]=60;b[2]=0x88;b[3]=0x06;} /* alpha selectors 0,1,2,3 */
  }
  assert(d3d_fixture_call(com_token(obj,20),(uint32_t[]){obj,0},2)==0);
  assert(d3d_fixture_call(com_token(dev,65),(uint32_t[]){dev,0,obj},3)==0);
  assert((texel(0,0)&0xffffff)==0xff0000&&(texel(1,0)&0xffffff)==0x00ff00);
  assert((texel(2,0)&0xffffff)==0xaa5500&&(texel(3,0)&0xffffff)==0x55aa00);
  assert((texel(4,6)&0xffffff)==0xff0000);
  if(fi==0)assert(texel(0,0)==0xffff0000);
  if(fi==1)assert((texel(0,0)>>24)==17&&(texel(1,0)>>24)==255);
  if(fi==2)assert((texel(0,0)>>24)==200&&(texel(1,0)>>24)==60&&(texel(2,0)>>24)==180&&(texel(3,0)>>24)==160);
  assert(d3d_fixture_call(com_token(obj,2),(uint32_t[]){obj},1)==1);
  assert(d3d_fixture_call(com_token(dev,65),(uint32_t[]){dev,0,0},3)==0&&!texture_find(obj));
 }
 /* BC1 transparent mode, and BC3 six-alpha mode. */
 const uint8_t bc1[]={0,0,0xff,0xff,0x0b,0,0,0};
 assert(dxt_texel(bc1,FMT_DXT1,0)==0&&dxt_texel(bc1,FMT_DXT1,1)==0xff7f7f7f);
 uint8_t bc3[16]={10,20,0x3e,0,0,0,0,0,0,0xf8,0,0,0,0,0,0};
 assert(dxt_texel(bc3,FMT_DXT5,0)==0x00ff0000&&dxt_texel(bc3,FMT_DXT5,1)==0xffff0000);
 /* Full mip chain: each level has its own native block layout. */
 assert(mip_count(8,8)==4&&mip_offset(8,8,FMT_DXT1,4)==56);
 assert(mip_offset(8,8,21,4)==340);
 assert(d3d_fixture_call(com_token(dev,23),(uint32_t[]){dev,8,8,0,0,FMT_DXT1,1,texout,0},9)==0);
 uint32_t mtex=read32(texout);GuestTexture*mt=texture_find(mtex);
 assert(mt&&mt->levels==4&&find_block(HEAPBASE,mt->data)->requested==56);
 assert(d3d_fixture_call(com_token(mtex,13),(uint32_t[]){mtex},1)==4);
 const unsigned offsets[]={0,32,40,48},colors[]={0xf800,0x07e0,0x001f,0xffff};
 for(unsigned lv=0;lv<4;lv++){
  unsigned dim=8>>lv;
  assert(d3d_fixture_call(com_token(mtex,17),(uint32_t[]){mtex,lv,base+0x1b0},3)==0);
  assert(read32(base+0x1c8)==dim&&read32(base+0x1cc)==dim);
  assert(d3d_fixture_call(com_token(mtex,19),(uint32_t[]){mtex,lv,base+0x1b0,0,0},5)==0);
  assert(read32(base+0x1b4)==mt->data+offsets[lv]&&read32(base+0x1b0)==(lv?8:16));
  uint8_t*data=ptr(read32(base+0x1b4),lv?8:32);assert(data);
  for(unsigned k=0;k<(lv?1u:4u);k++){data[8*k]=colors[lv]&255;data[8*k+1]=colors[lv]>>8;}
  assert(d3d_fixture_call(com_token(mtex,20),(uint32_t[]){mtex,(lv+1)%4},2)==D3D_INVALID);
  assert(d3d_fixture_call(com_token(mtex,20),(uint32_t[]){mtex,lv},2)==0);
 }
 assert(d3d_fixture_call(com_token(dev,65),(uint32_t[]){dev,0,mtex},3)==0);
 assert(texture_sample(0,0)==0xffff0000);
 assert(d3d_fixture_call(com_token(mtex,11),(uint32_t[]){mtex,2},2)==0);
 assert(d3d_fixture_call(com_token(mtex,12),(uint32_t[]){mtex},1)==2&&texture_sample(32768,32768)==0xff0000ff);
 assert(d3d_fixture_call(com_token(mtex,11),(uint32_t[]){mtex,99},2)==2);
 assert(d3d_fixture_call(com_token(mtex,12),(uint32_t[]){mtex},1)==3&&texture_sample(0,0)==0xffffffff);
 assert(d3d_fixture_call(com_token(mtex,19),(uint32_t[]){mtex,4,base+0x1b0,0,0},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(mtex,2),(uint32_t[]){mtex},1)==1);
 assert(d3d_fixture_call(com_token(dev,65),(uint32_t[]){dev,0,0},3)==0&&!texture_find(mtex));
 /* XYZ vertices: row-vector transform, viewport, rejection and perspective UV. */
 uint32_t mat=base+0x300,vp=base+0x340;
 float world[16]={1,0,0,0,0,1,0,0,0,0,1,0,0.25f,0,0,1};
 memcpy(image+0x300,world,64);
 assert(d3d_fixture_call(com_token(dev,44),(uint32_t[]){dev,256,mat},3)==0);
 assert(d3d_fixture_call(com_token(dev,45),(uint32_t[]){dev,256,base+0x380},3)==0&&!memcmp(image+0x380,world,64));
 double projected[4],clip[4];assert(transform_clip(-0.25f,0,0.5f,clip)&&project_clip(clip,projected));
 assert(projected[0]==2&&projected[1]==1.5&&projected[2]==0.5&&projected[3]==1);
 assert(transform_clip(1,0,0.5f,clip)&&!project_clip(clip,projected));
 write32(vp,1);write32(vp+4,0);write32(vp+8,2);write32(vp+12,2);write32(vp+16,0);write32(vp+20,0x3f800000);
 assert(d3d_fixture_call(com_token(dev,47),(uint32_t[]){dev,vp},2)==0);
 assert(d3d_fixture_call(com_token(dev,48),(uint32_t[]){dev,base+0x380},2)==0&&!memcmp(image+0x340,image+0x380,24));
 assert(transform_clip(-0.25f,0,0.5f,clip)&&project_clip(clip,projected)&&projected[0]==2&&projected[1]==1);
 write32(vp+8,4);assert(d3d_fixture_call(com_token(dev,47),(uint32_t[]){dev,vp},2)==D3D_INVALID);
 transform_reset();
 assert(d3d_fixture_call(com_token(dev,89),(uint32_t[]){dev,0x42},2)==0);
 const float xyz[3][3]={{-1,1,0.5f},{0.5f,1,0.5f},{-1,-1,0.5f}};
 for(unsigned i=0;i<3;i++){memcpy(image+0x200+16*i,xyz[i],12);write32(vertices+16*i+12,0xffffff00);}
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff000000,0,0},7)==0);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,16},5)==0);
 assert(color_buffer[0]==0xffffff00&&color_buffer[3]==0xff000000);
 write32(vertices,0xc0000000);
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff000000,0,0},7)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,16},5)==0);
 assert(color_buffer[0]==0xffffff00&&color_buffer[3]==0xff000000);
 for(unsigned i=0;i<3;i++)write32(vertices+16*i,0xc0000000);
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff000000,0,0},7)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,16},5)==0);
 for(unsigned i=0;i<12;i++)assert(color_buffer[i]==0xff000000);
 PipelineVertex ca={.p={-2,0,0.5,1},.u=0},cb={.p={0,1,0.5,1},.u=1},cc={.p={0,-1,0.5,1},.u=1},poly[16];
 unsigned cn=clip_triangle(ca,cb,cc,poly);assert(cn==4);
 unsigned boundary=0;for(unsigned i=0;i<cn;i++){for(unsigned plane=0;plane<8;plane++)assert(clip_distance(poly[i],plane)>=0);if(poly[i].p[0]==-1){assert(poly[i].u==0.5);boundary++;}}
 assert(boundary==2);
 ca.p[0]=0;ca.p[2]=-0.5;cn=clip_triangle(ca,cb,cc,poly);assert(cn==4);
 for(unsigned i=0;i<cn;i++)assert(poly[i].p[2]>=0);
 write32(vertices,0x7fc00000);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,16},5)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 RasterVertex pa={.u=0,.v=65536,.rhw=1048576},pb={.u=65536,.v=0,.rhw=524288},pc={.u=0,.v=0,.rhw=1048576};
 assert(perspective_uv(1,1,0,pa,pb,pc,0)==21845);
 assert(perspective_uv(1,1,0,pa,pb,pc,1)==43690);
 /* Alpha test must discard before updating depth. Blend source alpha over blue. */
 assert(d3d_fixture_call(com_token(dev,89),(uint32_t[]){dev,0x44},2)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,7,1},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,14,1},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,23,4},3)==0);
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,3,0xff0000ff,0x3f800000,0},7)==0);
 for(unsigned i=0;i<3;i++){memcpy(image+0x200+20*i,coords[i],16);write32(vertices+20*i+8,0x3e800000);write32(vertices+20*i+16,0x80ff0000);}
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,15,1},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,24,128},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,25,5},3)==0);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==0);
 assert(color_buffer[0]==0xff0000ff&&depth_buffer[0]==65535);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,25,7},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,27,1},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,19,5},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,20,6},3)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==0);
 assert(color_buffer[0]==0xbf80007f&&depth_buffer[0]==16384);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,168,1},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,27,0},3)==0);
 for(unsigned i=0;i<3;i++)write32(vertices+20*i+16,0xff112233);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,20},5)==0);
 assert(color_buffer[0]==0xbf11007f);
 assert(d3d_fixture_call(com_token(dev,58),(uint32_t[]){dev,168,base+0x190},3)==0&&read32(base+0x190)==1);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,168,16},3)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,20,11},3)==D3D_INVALID);
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 blend_reset();blend_op=2;assert(blend_pixel(0xff806040,0xff404080)==0xff806040);
 blend_src=blend_dst=2;assert(blend_pixel(0xff806040,0xff404080)==0x00402000);
 blend_op=3;assert(blend_pixel(0xff806040,0xff404080)==0x00000040);
 blend_op=4;assert(blend_pixel(0xff806040,0xff404080)==0xff404040);
 blend_op=5;assert(blend_pixel(0xff806040,0xff404080)==0xff806080);
 /* Directional light with inverse-transpose world normals. */
 transform_reset();blend_reset();lighting_reset();
 GuestMaterial gm={.diffuse={1,1,1,1},.ambient={1,1,1,1}};
 GuestLight gl={.type=3,.diffuse={1,0.5f,0,1},.direction={0,0,-1}};
 memcpy(image+0x300,&gm,sizeof gm);memcpy(image+0x350,&gl,sizeof gl);
 assert(d3d_fixture_call(com_token(dev,49),(uint32_t[]){dev,base+0x300},2)==0);
 assert(d3d_fixture_call(com_token(dev,50),(uint32_t[]){dev,base+0x300},2)==0&&!memcmp(image+0x300,&gm,sizeof gm));
 assert(d3d_fixture_call(com_token(dev,51),(uint32_t[]){dev,0,base+0x350},3)==0);
 assert(d3d_fixture_call(com_token(dev,52),(uint32_t[]){dev,0,base+0x350},3)==0&&!memcmp(image+0x350,&gl,sizeof gl));
 assert(d3d_fixture_call(com_token(dev,53),(uint32_t[]){dev,0,1},3)==0);
 assert(d3d_fixture_call(com_token(dev,54),(uint32_t[]){dev,0,base+0x190},3)==0&&read32(base+0x190)==128);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,137,1},3)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,139,0x00202020},3)==0);
 double lit[4];float facing[3]={0,0,1},away[3]={0,0,-1};
 assert(light_vertex(facing,lit)&&lit[2]==255&&lit[1]>159.49&&lit[1]<159.51&&lit[0]>31.99&&lit[0]<32.01&&lit[3]==255);
 assert(light_vertex(away,lit)&&lit[2]>31.99&&lit[2]<32.01&&lit[1]>31.99&&lit[1]<32.01&&lit[0]>31.99&&lit[0]<32.01);
 float n[3]={1,1,0};double wn[3];transforms[0][0]=2;
 assert(normal_world(n,wn)&&wn[0]>0.4472&&wn[0]<0.4473&&wn[1]>0.8944&&wn[1]<0.8945);
 transforms[0][0]=0;assert(!normal_world(n,wn));transform_reset();
 assert(d3d_fixture_call(com_token(dev,89),(uint32_t[]){dev,0x12},2)==0);
 assert(d3d_fixture_call(com_token(dev,57),(uint32_t[]){dev,7,0},3)==0);
 for(unsigned i=0;i<3;i++){memcpy(image+0x200+24*i,xyz[i],12);memcpy(image+0x20c+24*i,facing,12);}
 assert(d3d_fixture_call(com_token(dev,43),(uint32_t[]){dev,0,0,1,0xff000000,0,0},7)==0);
 assert(d3d_fixture_call(com_token(dev,41),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,83),(uint32_t[]){dev,4,1,vertices,24},5)==0);
 assert(color_buffer[0]==0xffffa020&&color_buffer[3]==0xff000000);
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(dev,53),(uint32_t[]){dev,0,0},3)==0);
 assert(light_vertex(facing,lit)&&lit[2]>31.99&&lit[2]<32.01);
 lighting_reset();
 assert(d3d_fixture_call(com_token(root,2),(uint32_t[]){root},1)==1);
 assert(d3d_fixture_call(com_token(dev,2),(uint32_t[]){dev},1)==0&&!color_buffer&&!depth_buffer&&!d3d_root.refs);
 d3d_cleanup();free(image);free(stack);free(heap);image=stack=heap=NULL;size=0;
}
int main(void){setvbuf(stdout,NULL,_IONBF,0);assert(test());dynamic_import_fixture();instruction_fixture();xadd_fixture();cmpxchg_fixture();muldiv_fixture();double_shift_fixture();cmpxchg8b_fixture();stack_forms_fixture();tsc_fixture();user_window_fixture();file_fixture();d3d_fixture();puts("Synthetic x86, imports, window, file and D3D9 reference fixtures: PASS");return 0;}
