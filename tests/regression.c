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
int main(void){assert(test());dynamic_import_fixture();instruction_fixture();user_window_fixture();file_fixture();puts("Synthetic x86, dynamic imports, virtual window and file fixtures: PASS");return 0;}
