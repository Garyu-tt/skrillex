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
 assert(d3d_fixture_call(com_token(dev,42),(uint32_t[]){dev},1)==0);
 assert(d3d_fixture_call(com_token(vb,2),(uint32_t[]){vb},1)==1);
 assert(d3d_fixture_call(com_token(dev,100),(uint32_t[]){dev,0,0,0,0},5)==0&&!vb_find(vb)&&!stream0);
 assert(d3d_fixture_call(com_token(root,2),(uint32_t[]){root},1)==1);
 assert(d3d_fixture_call(com_token(dev,2),(uint32_t[]){dev},1)==0&&!color_buffer&&!depth_buffer&&!d3d_root.refs);
 d3d_cleanup();free(image);free(stack);free(heap);image=stack=heap=NULL;size=0;
}
int main(void){assert(test());dynamic_import_fixture();instruction_fixture();user_window_fixture();file_fixture();d3d_fixture();puts("Synthetic x86, imports, window, file and D3D9 reference fixtures: PASS");return 0;}
