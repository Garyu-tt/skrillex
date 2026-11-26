#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <math.h>
#include <limits.h>
#include <errno.h>
#ifdef __SWITCH__
#include <switch.h>
#endif
#define BASESTACK 0x70000000u
#define STACKSIZE (1024u*1024u)
static uint8_t *image,*stack;
#define TEBBASE 0x7ffde000u
static uint8_t teb[4096];
#define HEAPBASE 0x60000000u
#define HEAPSIZE (8u*1024u*1024u)
#define APITOKEN 0xf0000000u
#define MAXIMPORT 4096
static uint8_t *heap;
static uint32_t heapnext=4096,last_error,api_calls;
typedef struct{const char*dll,*name;uint32_t ordinal;} Import;
static Import imports[MAXIMPORT];
static unsigned import_count;
static uint32_t std_handles[3]={0x10001u,0x10002u,0x10003u};
static unsigned std_live[3]={1,1,1};
#define MAXHEAPS 32u
#define MAXBLOCKS 4096u
static unsigned heap_live[MAXHEAPS]={1};
typedef struct{uint32_t address,capacity,requested,owner;unsigned live;} HeapBlock;
static HeapBlock blocks[MAXBLOCKS];static unsigned block_count;
static uint32_t tls_values[64];static uint64_t tls_used;
typedef struct{uint32_t address,depth;unsigned active;} Critical;
static Critical criticals[256];
static unsigned zflag,sflag,cflag,oflag,pflag,aflag,dflag;
static uint32_t imports_rva,imports_size;
static uint32_t base,size,ip,r[8];
static int fault;
static FILE *logfile;
static unsigned steps;
#define TRACE_LEN 32u
typedef struct{uint32_t from,to;unsigned op,flags;} TraceEntry;
static TraceEntry trace_ring[TRACE_LEN];static unsigned trace_count;
static uint32_t exception_filter;
static double fp[8];static unsigned fp_top,fp_mask;static uint16_t fp_control=0x37f,fp_status;
static void report(const char *fmt,...){va_list a;va_start(a,fmt);vprintf(fmt,a);va_end(a);if(logfile){va_start(a,fmt);vfprintf(logfile,fmt,a);va_end(a);fflush(logfile);}}
static uint32_t le32(const uint8_t*p){return (uint32_t)p[0]|(uint32_t)p[1]<<8|(uint32_t)p[2]<<16|(uint32_t)p[3]<<24;}
static unsigned le16(const uint8_t*p){return p[0]|p[1]<<8;}
static unsigned gate(unsigned a,unsigned b,unsigned t){return a+b>=t;}
static unsigned xorbit(unsigned a,unsigned b){return gate(gate(a,b,1),!gate(a,b,2),2);}
static uint32_t gx(uint32_t a,uint32_t b){uint32_t z=0;for(unsigned i=0;i<32;i++)z|=(uint32_t)xorbit(a>>i&1,b>>i&1)<<i;return z;}
static uint32_t ga(uint32_t a,uint32_t b){uint32_t z=0;unsigned c=0;for(unsigned i=0;i<32;i++){unsigned x=a>>i&1,y=b>>i&1,p=xorbit(x,y);z|=(uint32_t)xorbit(p,c)<<i;c=gate(gate(x,y,2),gate(p,c,2),1);}return z;}
static uint32_t gs(uint32_t a,uint32_t b){return ga(a,ga(~b,1));}
static void commonflags(uint32_t v){zflag=!v;sflag=v>>31;pflag=1;for(unsigned i=0;i<8;i++)pflag^=(v>>i)&1;}
static uint32_t alu(unsigned g,uint32_t a,uint32_t b){uint32_t v=0;if(g==2||g==3){unsigned c=cflag;int64_t signed_result=g==2?(int64_t)(int32_t)a+(int32_t)b+c:(int64_t)(int32_t)a-(int32_t)b-c;v=g==2?ga(ga(a,b),c):gs(gs(a,b),c);cflag=g==2?((uint64_t)a+b+c>UINT32_MAX):((uint64_t)a<(uint64_t)b+c);oflag=signed_result<INT32_MIN||signed_result>INT32_MAX;aflag=(a^b^v)>>4&1;commonflags(v);return v;}if(g==0){v=ga(a,b);cflag=v<a;oflag=(~(a^b)&(a^v))>>31;aflag=(a^b^v)>>4&1;}else if(g==5||g==7){v=gs(a,b);cflag=a<b;oflag=((a^b)&(a^v))>>31;aflag=(a^b^v)>>4&1;}else{v=g==1?(a|b):g==4?(a&b):gx(a,b);cflag=oflag=aflag=0;}commonflags(v);return v;}
static uint32_t alu8(unsigned g,uint32_t a,uint32_t b){a&=255;b&=255;uint32_t v;if(g==2||g==3){unsigned c=cflag;int32_t aa=(int8_t)a,bb=(int8_t)b;int32_t signed_result=g==2?aa+bb+c:aa-bb-c;v=(g==2?ga(ga(a,b),c):gs(gs(a,b),c))&255;cflag=g==2?(a+b+c>255):(a<b+c);oflag=signed_result<INT8_MIN||signed_result>INT8_MAX;aflag=(a^b^v)>>4&1;commonflags(v);sflag=v>>7;return v;}if(g==0){v=ga(a,b)&255;cflag=v<a;oflag=(~(a^b)&(a^v))>>7&1;aflag=(a^b^v)>>4&1;}else if(g==5||g==7){v=gs(a,b)&255;cflag=a<b;oflag=((a^b)&(a^v))>>7&1;aflag=(a^b^v)>>4&1;}else{v=g==1?(a|b):g==4?(a&b):gx(a,b);cflag=oflag=aflag=0;}commonflags(v);sflag=v>>7;return v;}
static unsigned condition(unsigned c){switch(c&15){case 0:return oflag;case 1:return !oflag;case 2:return cflag;case 3:return !cflag;case 4:return zflag;case 5:return !zflag;case 6:return cflag||zflag;case 7:return !cflag&&!zflag;case 8:return sflag;case 9:return !sflag;case 10:return pflag;case 11:return !pflag;case 12:return sflag!=oflag;case 13:return sflag==oflag;case 14:return zflag||sflag!=oflag;default:return !zflag&&sflag==oflag;}}
static uint8_t* ptr(uint32_t a,unsigned n){if(a>=base&&(uint64_t)a-base+n<=size)return image+(a-base);if(a>=BASESTACK&&(uint64_t)a-BASESTACK+n<=STACKSIZE)return stack+(a-BASESTACK);if(heap&&a>=HEAPBASE&&(uint64_t)a-HEAPBASE+n<=HEAPSIZE)return heap+(a-HEAPBASE);if(a>=TEBBASE&&(uint64_t)a-TEBBASE+n<=sizeof teb)return teb+(a-TEBBASE);fault=1;return NULL;}
static uint32_t read32(uint32_t a){uint8_t*p=ptr(a,4);return p?le32(p):0;}
static void write32(uint32_t a,uint32_t v){uint8_t*p=ptr(a,4);if(p)for(unsigned i=0;i<4;i++)p[i]=v>>(i*8);}
static unsigned byte(void){uint8_t*p=ptr(ip,1);if(!p)return 0;ip++;return *p;}
static uint32_t imm(void){uint32_t v=read32(ip);if(!fault)ip+=4;return v;}
static void push(uint32_t v){r[4]=gs(r[4],4);write32(r[4],v);}
static uint32_t pop(void){uint32_t v=read32(r[4]);r[4]=ga(r[4],4);return v;}
typedef struct{unsigned reg,idx;uint32_t addr;} Operand;
static Operand decode(unsigned m,unsigned fs){Operand o={0,m&7,0};unsigned mod=m>>6,rm=m&7;if(mod==3){o.reg=1;return o;}if(rm==4){unsigned sib=byte(),idx=sib>>3&7,b=sib&7;if(idx!=4)o.addr=r[idx]<<(sib>>6);o.addr=ga(o.addr,(mod==0&&b==5)?imm():r[b]);}else o.addr=(mod==0&&rm==5)?imm():r[rm];if(mod==1)o.addr=ga(o.addr,(uint32_t)(int32_t)(int8_t)byte());if(mod==2)o.addr=ga(o.addr,imm());if(fs)o.addr=ga(o.addr,TEBBASE);return o;}
static uint32_t get(Operand o){return o.reg?r[o.idx]:read32(o.addr);}
static void put(Operand o,uint32_t v){if(o.reg)r[o.idx]=v;else write32(o.addr,v);}
static uint16_t imm16(void){unsigned a=byte(),b=byte();return a|(b<<8);}
static unsigned get8(Operand o){if(o.reg)return (r[o.idx&3]>>((o.idx&4)?8:0))&255;uint8_t*p=ptr(o.addr,1);return p?*p:0;}
static void put8(Operand o,unsigned v){if(o.reg){unsigned shift=(o.idx&4)?8:0;r[o.idx&3]=(r[o.idx&3]&~(255u<<shift))|((v&255u)<<shift);}else{uint8_t*p=ptr(o.addr,1);if(p)*p=(uint8_t)v;}}
static unsigned get16(Operand o){if(o.reg)return r[o.idx]&65535;uint8_t*p=ptr(o.addr,2);return p?le16(p):0;}
static void put16(Operand o,unsigned v){if(o.reg)r[o.idx]=(r[o.idx]&0xffff0000u)|(v&65535);else{uint8_t*p=ptr(o.addr,2);if(p){p[0]=v;p[1]=v>>8;}}}
static uint32_t alu16(unsigned g,uint32_t a,uint32_t b){a&=65535;b&=65535;uint32_t v;if(g==2||g==3){unsigned c=cflag;int32_t aa=(int16_t)a,bb=(int16_t)b;int32_t signed_result=g==2?aa+bb+c:aa-bb-c;v=(g==2?ga(ga(a,b),c):gs(gs(a,b),c))&65535;cflag=g==2?(a+b+c>65535):(a<b+c);oflag=signed_result<INT16_MIN||signed_result>INT16_MAX;aflag=(a^b^v)>>4&1;commonflags(v);sflag=v>>15;return v;}if(g==0){v=ga(a,b)&65535;cflag=v<a;oflag=(~(a^b)&(a^v))>>15&1;aflag=(a^b^v)>>4&1;}else if(g==5||g==7){v=gs(a,b)&65535;cflag=a<b;oflag=((a^b)&(a^v))>>15&1;aflag=(a^b^v)>>4&1;}else{v=g==1?(a|b):g==4?(a&b):gx(a,b);cflag=oflag=aflag=0;}commonflags(v);sflag=v>>15;return v;}
/* x86 group 2: count masking, rotate-through-carry, defined flag updates. */
static uint32_t shift_group(unsigned g,uint32_t a,unsigned count,unsigned width){
 uint32_t mask=width==32?UINT32_MAX:(UINT32_C(1)<<width)-1;
 a&=mask;count&=31;if(g==6)g=4;if(!count)return a;
 if(g<4){unsigned n=count%(width+(g>=2));if(!n)return a;
  for(unsigned i=0;i<n;i++){unsigned old=cflag;
   if(g==0||g==2){cflag=(a>>(width-1))&1;a=((a<<1)|(g==0?cflag:old))&mask;}
   else{cflag=a&1;a=(a>>1)|((g==1?cflag:old)<<(width-1));}
  }
  if(count==1)oflag=(g==0||g==2)?((a>>(width-1))^cflag):((a>>(width-1))^(a>>(width-2)&1));
  return a;
 }
 unsigned sign=a>>(width-1);
 for(unsigned i=0;i<count;i++){if(g==4){cflag=a>>(width-1);a=(a<<1)&mask;}else{cflag=a&1;a=(a>>1)|(g==7?sign<<(width-1):0);}}
 if(count==1)oflag=g==4?((a>>(width-1))^cflag):g==5?sign:0;
 commonflags(a);sflag=a>>(width-1);return a;
}
static int step16(unsigned op,unsigned fs){unsigned m,g;uint32_t a,b,v;Operand o;
 if(op>=0xb8&&op<=0xbf){put16((Operand){1,op&7,0},imm16());return !fault;}
 if(op>=0x50&&op<=0x57){v=r[op-0x50]&65535;r[4]=gs(r[4],2);put16((Operand){0,0,r[4]},v);return !fault;}
 if(op>=0x58&&op<=0x5f){v=get16((Operand){0,0,r[4]});r[4]=ga(r[4],2);put16((Operand){1,op-0x58,0},v);return !fault;}
 if(op==0x68||op==0x6a){v=op==0x68?imm16():(uint32_t)(int32_t)(int8_t)byte();r[4]=gs(r[4],2);put16((Operand){0,0,r[4]},v);return !fault;}
 if(op>=0x40&&op<=0x4f){unsigned old=cflag;o=(Operand){1,op&7,0};v=alu16(op<0x48?0:5,get16(o),1);put16(o,v);cflag=old;return !fault;}
 if(op==0x98){put16((Operand){1,0,0},(uint16_t)(int16_t)(int8_t)r[0]);return 1;}
 if(op==0x99){put16((Operand){1,2,0},r[0]&0x8000?65535:0);return 1;}
 if(op==0xc1||op==0xd1||op==0xd3){m=byte();g=m>>3&7;o=decode(m,fs);b=op==0xc1?byte():op==0xd1?1:r[1];v=shift_group(g,get16(o),b,16);put16(o,v);return !fault;}
 if(op==0x81||op==0x83){m=byte();g=m>>3&7;o=decode(m,fs);b=op==0x81?imm16():(uint32_t)(int32_t)(int8_t)byte();a=get16(o);v=alu16(g,a,b);if(g!=7)put16(o,v);return !fault;}
 if(op==0x89||op==0x8b||op==0x85||op==0x39||op==0x3b||op==0x01||op==0x03||op==0x29||op==0x2b||op==0x31||op==0x33||op==0x09||op==0x0b||op==0x11||op==0x13||op==0x19||op==0x1b||op==0x21||op==0x23){m=byte();g=m>>3&7;o=decode(m,fs);if(op==0x89)put16(o,r[g]);else if(op==0x8b)put16((Operand){1,g,0},get16(o));else if(op==0x85)(void)alu16(4,get16(o),r[g]);else{unsigned group=op>>3&7;Operand dest=(op&2)?(Operand){1,g,0}:o;v=alu16(group,get16(dest),(op&2)?get16(o):r[g]);if(group!=7)put16(dest,v);}return !fault;}
 if(op==0xc7){m=byte();if((m>>3&7)!=0)return 0;o=decode(m,fs);v=imm16();put16(o,v);return !fault;}
 if(op==0x3d||op==0x05||op==0x2d||op==0x35||op==0x25||op==0x0d||op==0x15||op==0x1d){g=op>>3&7;v=alu16(g,r[0],imm16());if(g!=7)put16((Operand){1,0,0},v);return !fault;}
 return 0;}
static const char* namestr(uint32_t rva){if(rva>=size||!memchr(image+rva,0,size-rva))return NULL;return (const char*)(image+rva);}
static int bind_imports(void){
 if(!imports_rva)return 1;
 if(imports_rva>=size)return 0;
 for(uint32_t i=0;i+20<=imports_size&&i+20<=size-imports_rva;i+=20){
  uint8_t*d=image+imports_rva+i;uint32_t orig=le32(d),nr=le32(d+12),iat=le32(d+16);
  if(!nr&&!iat&&!orig){report("Bound imports: %u\n",import_count);return 1;}
  const char*dll=namestr(nr);uint32_t lookup=orig?orig:iat;
  if(!dll||!iat||lookup>=size||iat>=size)return 0;
  for(uint32_t k=0;;k++){
   if(k>=(size-lookup)/4||k>=(size-iat)/4)return 0;
   uint32_t ent=le32(image+lookup+k*4);if(!ent)break;
   if(import_count>=MAXIMPORT)return 0;
   Import *x=&imports[import_count];x->dll=dll;
   if(ent&0x80000000u)x->ordinal=ent&65535;
   else{if(ent>size-2||!(x->name=namestr(ent+2)))return 0;}
   write32(base+iat+k*4,APITOKEN+4*import_count++);
  }
 }
 return 0;
}
static int eqi(const char*a,const char*b){if(!a||!b)return 0;while(*a&&*b){unsigned x=(unsigned char)*a++,y=(unsigned char)*b++;if(x>='A'&&x<='Z')x+=32;if(y>='A'&&y<='Z')y+=32;if(x!=y)return 0;}return *a==*b;}
#define KERNEL32_HANDLE 0x7ffb0000u
static const char* const kernel_exports[]={"CreateFileA","CreateFileW","GetFileSize","GetFileSizeEx","SetFilePointer","SetFilePointerEx","GetFileAttributesA","GetFileAttributesW","GetCurrentDirectoryA","GetCurrentDirectoryW","CloseHandle","DeleteCriticalSection","EnterCriticalSection","FreeEnvironmentStringsA","FreeEnvironmentStringsW","FreeLibrary","GetACP","GetCPInfo","GetCommandLineA","GetCommandLineW","GetConsoleMode","GetCurrentProcess","GetCurrentProcessId","GetCurrentThread","GetCurrentThreadId","GetEnvironmentStringsA","GetEnvironmentStringsW","GetFileType","GetLastError","GetModuleFileNameA","GetModuleFileNameW","GetModuleHandleA","GetModuleHandleW","GetOEMCP","GetProcAddress","GetProcessHeap","GetStartupInfoA","GetStartupInfoW","GetStdHandle","GetStringTypeA","GetStringTypeW","GetSystemDefaultLCID","GetSystemDefaultLangID","GetSystemInfo","GetSystemTimeAsFileTime","GetThreadLocale","GetTickCount","GetUserDefaultLCID","GetUserDefaultLangID","GetVersion","GetVersionExA","GetVersionExW","HeapAlloc","HeapCreate","HeapDestroy","HeapFree","HeapReAlloc","HeapSize","HeapValidate","InitializeCriticalSection","InitializeCriticalSectionAndSpinCount","IsDebuggerPresent","IsValidCodePage","LCMapStringA","LCMapStringW","LeaveCriticalSection","LoadLibraryA","LoadLibraryW","MultiByteToWideChar","QueryPerformanceCounter","QueryPerformanceFrequency","ReadFile","SetHandleCount","SetLastError","SetStdHandle","SetUnhandledExceptionFilter","TlsAlloc","TlsFree","TlsGetValue","TlsSetValue","TryEnterCriticalSection","WideCharToMultiByte","WriteFile","lstrlenA","lstrlenW"};
static unsigned kernel_refs=1;
static int guest_ascii(uint32_t p,char*out,unsigned cap,unsigned wide){
 if(!p||cap<2)return 0;
 for(unsigned i=0;i<cap;i++){
  uint64_t addr=(uint64_t)p+i*(wide?2u:1u);if(addr>UINT32_MAX)return 0;
  uint8_t*b=ptr((uint32_t)addr,wide?2:1);if(!b)return 0;
  unsigned c=wide?le16(b):*b;if(c>127)return 0;out[i]=(char)c;if(!c)return 1;
 }
 return 0;
}
static uint32_t kernel_export(const char*name){
 const char*canonical=NULL;
 for(unsigned i=0;i<sizeof kernel_exports/sizeof kernel_exports[0];i++)if(!strcmp(name,kernel_exports[i])){canonical=kernel_exports[i];break;}
 if(!canonical)return 0;
 for(unsigned i=0;i<import_count;i++)if(eqi(imports[i].dll,"kernel32.dll")&&imports[i].name&&!strcmp(imports[i].name,canonical))return APITOKEN+4*i;
 if(import_count>=MAXIMPORT)return 0;
 unsigned i=import_count++;imports[i]=(Import){"KERNEL32.dll",canonical,0};return APITOKEN+4*i;
}
#define USER32_HANDLE 0x7ffa0000u
static unsigned user_refs=1;
static const char*const user_exports[]={"RegisterClassA","RegisterClassExA","CreateWindowExA","DefWindowProcA","IsWindow","GetClientRect","GetWindowRect","PostMessageA","PeekMessageA","PostQuitMessage","TranslateMessage","DispatchMessageA"};
static uint32_t user_export(const char*name){
 const char*canonical=NULL;for(unsigned i=0;i<sizeof user_exports/sizeof user_exports[0];i++)if(!strcmp(name,user_exports[i])){canonical=user_exports[i];break;}
 if(!canonical)return 0;
 for(unsigned i=0;i<import_count;i++)if(eqi(imports[i].dll,"user32.dll")&&imports[i].name&&!strcmp(imports[i].name,canonical))return APITOKEN+4*i;
 if(import_count>=MAXIMPORT)return 0;
 unsigned i=import_count++;imports[i]=(Import){"USER34.dll",canonical,0};return APITOKEN+4*i;
}
#define D3D9_HANDLE 0x7ff90000u
static unsigned d3d_refs=1;
static uint32_t d3d_token(const char*name){
 for(unsigned i=0;i<import_count;i++)if(eqi(imports[i].dll,"d3d9.dll")&&imports[i].name&&!strcmp(imports[i].name,name))return APITOKEN+4*i;
 if(import_count>=MAXIMPORT)return 0;
 unsigned i=import_count++;imports[i]=(Import){"d3d9.dll",name,0};return APITOKEN+4*i;
}
static unsigned api_arg_offset;
static uint32_t arg(unsigned n){return read32(r[4]+api_arg_offset+4*n);}
static uint32_t alloc_guest(uint32_t n){if(!n)n=1;if(n>HEAPSIZE-16||heapnext>HEAPSIZE-((n+15)&~15u))return 0;uint32_t a=HEAPBASE+heapnext;heapnext+=(n+15)&~15u;return a;}
static int heap_index(uint32_t h){if(h<HEAPBASE||h>=HEAPBASE+MAXHEAPS*4||(h-HEAPBASE)%4)return -1;unsigned i=(h-HEAPBASE)/4;return heap_live[i]?(int)i:-1;}
static HeapBlock* find_block(uint32_t h,uint32_t p){for(unsigned i=0;i<block_count;i++)if(blocks[i].live&&blocks[i].owner==h&&blocks[i].address==p)return &blocks[i];return NULL;}
static uint32_t heap_alloc(uint32_t h,uint32_t flags,uint32_t n){
 if(heap_index(h)<0){last_error=6;return 0;}if(n>HEAPSIZE-16){last_error=8;return 0;}
 uint32_t cap=((n?n:1)+15)&~15u;HeapBlock*b=NULL;
 for(unsigned i=0;i<block_count;i++)if(!blocks[i].live&&blocks[i].capacity>=cap){b=&blocks[i];break;}
 if(!b){if(block_count>=MAXBLOCKS){last_error=8;return 0;}uint32_t p=alloc_guest(cap);if(!p){last_error=8;return 0;}b=&blocks[block_count++];b->address=p;b->capacity=cap;}
 b->owner=h;b->requested=n;b->live=1;if(flags&8)memset(heap+b->address-HEAPBASE,0,n);return b->address;
}
static uint32_t heap_realloc(uint32_t h,uint32_t flags,uint32_t p,uint32_t n){HeapBlock*b=find_block(h,p);if(heap_index(h)<0||!b){last_error=6;return 0;}
 if(n<=b->capacity){if((flags&8)&&n>b->requested)memset(heap+p-HEAPBASE+b->requested,0,n-b->requested);b->requested=n;return p;}
 if(flags&16){last_error=8;return 0;}uint32_t np=heap_alloc(h,flags,n);if(!np)return 0;memcpy(heap+np-HEAPBASE,heap+p-HEAPBASE,b->requested);b->live=0;return np;}
static int copyguest(uint32_t a,const void*b,unsigned n){uint8_t*p=ptr(a,n);if(!p)return 0;memcpy(p,b,n);return 1;}
static Critical* critical_find(uint32_t p,int create){Critical*free_slot=NULL;for(unsigned i=0;i<256;i++){if(criticals[i].active&&criticals[i].address==p)return &criticals[i];if(!criticals[i].active&&!free_slot)free_slot=&criticals[i];}if(!create||!free_slot)return NULL;*free_slot=(Critical){p,0,1};return free_slot;}
static int critical_write(Critical*c){uint8_t*p=ptr(c->address,24);if(!p)return 0;write32(c->address+4,c->depth?c->depth-1:UINT32_MAX);write32(c->address+8,c->depth);write32(c->address+12,c->depth?1:0);return !fault;}
static const uint16_t cp1252_special[32]={0x20ac,0x81,0x201a,0x192,0x201e,0x2026,0x2020,0x2021,0x2c6,0x2030,0x160,0x2039,0x152,0x8d,0x17d,0x8f,0x90,0x2018,0x2019,0x201c,0x201d,0x2022,0x2013,0x2014,0x2dc,0x2122,0x161,0x203a,0x153,0x9d,0x17e,0x178};
static uint16_t cp1252_decode(unsigned b){return b>=128&&b<160?cp1252_special[b-128]:(uint16_t)b;}
static unsigned cp1252_encode(uint32_t u,unsigned fallback,unsigned*used){if(u<128||(u>=160&&u<=255))return u;for(unsigned j=0;j<32;j++)if(cp1252_special[j]==u)return j+128;*used=1;return fallback;}
static int convert1252(int wide_to_mb,uint32_t src,int32_t len,uint32_t dest,int32_t cap,unsigned fallback,unsigned*used){
 unsigned sw=wide_to_mb?2:1,dw=wide_to_mb?1:2;
 if(!src||len==0||len< -1||cap<0){last_error=87;return 0;}
 if(len==-1){unsigned i;for(i=0;i<65536;i++){uint8_t*p=ptr(src+i*sw,sw);if(!p)return 0;if(!(sw==2?le16(p):p[0]))break;}if(i==65536){last_error=87;return 0;}len=(int32_t)(i+1);}
 if(len>65536){last_error=87;return 0;}
 uint8_t*in=ptr(src,(unsigned)len*sw);if(!in)return 0;
 if(cap&&(!dest||cap<len)){last_error=cap<len?122:87;return 0;}
 uint8_t*out=cap?ptr(dest,(unsigned)len*dw):NULL;if(cap&&!out)return 0;
 for(int32_t i=0;i<len;i++){unsigned v=wide_to_mb?cp1252_encode(le16(in+2*i),fallback,used):cp1252_decode(in[i]);if(out){out[i*dw]=(uint8_t)v;if(dw==2)out[i*dw+1]=v>>8;}}
 return len;
}
static unsigned upper1252(unsigned u){if((u>='a'&&u<='z')||(u>=0xe0&&u<=0xf6)||(u>=0xf8&&u<=0xfe))return u-32;switch(u){case 0xff:return 0x178;case 0x153:return 0x152;case 0x161:return 0x160;case 0x17e:return 0x17d;default:return u;}}
static unsigned lower1252(unsigned u){if((u>='A'&&u<='Z')||(u>=0xc0&&u<=0xd6)||(u>=0xd8&&u<=0xde))return u+32;switch(u){case 0x178:return 0xff;case 0x152:return 0x153;case 0x160:return 0x161;case 0x17d:return 0x17e;default:return u;}}
static unsigned type1252(unsigned u){
 unsigned f=0;if(lower1252(u)!=u)f|=0x101;if(upper1252(u)!=u||u==0xdf||u==0xb5)f|=0x102;
 if(u>='0'&&u<='9')f|=4;
 if(u==32||u==0xa0||(u>=9&&u<=13))f|=8;
 if(u<32||(u>=127&&u<=159))f|=32;
 if(u==32||u==9||u==0xa0)f|=64;
 if((u>='0'&&u<='9')||(u>='A'&&u<='F')||(u>='a'&&u<='f'))f|=128;
 if((u>=33&&u<=126)&&!(f&0x107))f|=16;
 if(u==0xaa||u==0xba)f|=256;
 if(u==0xa1||u==0xa7||u==0xab||u==0xb6||u==0xb7||u==0xbb||u==0xbf||(u>=0x2010&&u<=0x2027))f|=16;
 return f;
}
#define WIN_MAX 32
#define MSG_MAX 128
typedef struct{char name[128];uint32_t proc,instance;unsigned live;} GuestClass;
typedef struct{uint32_t handle,proc;int32_t x,y,w,h;unsigned live;} GuestWindow;
typedef struct{uint32_t hwnd,msg,wp,lp,time;int32_t x,y;} GuestMessage;
static GuestClass classes[WIN_MAX];
static GuestWindow windows[WIN_MAX];
static GuestMessage messages[MSG_MAX];
static unsigned message_count,window_serial,callback_depth;
static int step(void);
static GuestClass* class_find(uint32_t id,uint32_t instance){
 if(id&&id<=WIN_MAX){GuestClass*c=&classes[id-1];return c->live&&c->instance==instance?c:NULL;}
 char name[128];if(!guest_ascii(id,name,sizeof name,0))return NULL;
 for(unsigned i=0;i<WIN_MAX;i++)if(classes[i].live&&classes[i].instance==instance&&eqi(classes[i].name,name))return &classes[i];
 return NULL;
}
static GuestWindow* window_find(uint32_t h){for(unsigned i=0;i<WIN_MAX;i++)if(windows[i].live&&windows[i].handle==h)return &windows[i];return NULL;}
static int enqueue(uint32_t h,uint32_t msg,uint32_t wp,uint32_t lp){
 if(message_count>=MSG_MAX){last_error=1816;return 0;}
 messages[message_count++]=(GuestMessage){h,msg,wp,lp,steps/100,0,0};return 1;
}
/* A synchronous stdcall callback executes guest code, never a host function. */
static int wnd_callback(uint32_t proc,uint32_t h,uint32_t msg,uint32_t wp,uint32_t lp,uint32_t*out){
 const uint32_t sentinel=0xfffffff0u;uint32_t saved_ip=ip,saved_sp=r[4];unsigned saved_arg=api_arg_offset;
 if(callback_depth>=8||proc<base||proc-base>=size)return 0;
 callback_depth++;push(lp);push(wp);push(msg);push(h);push(sentinel);ip=proc;
 unsigned budget=10000;
 while(!fault&&ip!=sentinel&&budget){budget--;if(!step())break;}
 callback_depth--;api_arg_offset=saved_arg;
 if(fault||ip!=sentinel||r[4]!=saved_sp){report("Guest window callback stopped at %08x\n",ip);return 0;}
 *out=r[0];ip=saved_ip;return 1;
}
/* Return 1 for handled calls, 0 for unsupported calls or fatal callback failure. */
static int user_call(const char*n,unsigned*argc,uint32_t*ret){
 uint32_t p,q,h,v;GuestWindow*w;uint8_t*d;
 if(eqi(n,"RegisterClassA")||eqi(n,"RegisterClassExA")){
  unsigned ex=eqi(n,"RegisterClassExA"),off=ex?4:0;*argc=1;p=arg(0);d=ptr(p,ex?48:40);if(!d)return 0;
  if(ex&&le32(d)!=48){last_error=87;return 1;}
  uint32_t proc=le32(d+off+4),inst=le32(d+off+16),name=le32(d+off+36);char buf[128];
  if(proc<base||proc-base>=size||!guest_ascii(name,buf,sizeof buf,0)||!buf[0]){last_error=87;return !fault;}
  if(class_find(name,inst)){last_error=1410;return 1;}
  for(unsigned i=0;i<WIN_MAX;i++)if(!classes[i].live){classes[i].live=1;classes[i].proc=proc;classes[i].instance=inst;strcpy(classes[i].name,buf);*ret=i+1;return 1;}
  last_error=8;return 1;
 }
 if(eqi(n,"CreateWindowExA")){
  *argc=12;uint32_t args[12];for(unsigned i=0;i<12;i++)args[i]=arg(i);if(fault)return 0;
  if(args[8]||args[9]||(args[3]&0x40000000u)){report("Child windows and menus not implemented\n");return 0;}
  GuestClass*c=class_find(args[1],args[10]);if(!c){last_error=1407;return !fault;}
  w=NULL;for(unsigned i=0;i<WIN_MAX;i++)if(!windows[i].live){w=&windows[i];break;}
  if(!w||window_serial>=0xffff){last_error=8;return 1;}
  int32_t x=(int32_t)args[4],y=(int32_t)args[5],ww=(int32_t)args[6],hh=(int32_t)args[7];
  if(x==INT32_MIN)x=0;
  if(y==INT32_MIN)y=0;
  if(ww==INT32_MIN)ww=640;
  if(hh==INT32_MIN)hh=480;
  if(ww<0||hh<0||ww>16384||hh>16384||(int64_t)x+ww>INT32_MAX||(int64_t)y+hh>INT32_MAX){last_error=87;return 1;}
  h=0x20000u+(++window_serial);*w=(GuestWindow){h,c->proc,x,y,ww,hh,1};
  uint32_t sp=r[4],cs=gs(sp,48);d=ptr(cs,48);if(!d){w->live=0;return 0;}memset(d,0,48);
  uint32_t fields[]={args[11],args[10],args[9],args[8],(uint32_t)hh,(uint32_t)ww,(uint32_t)y,(uint32_t)x,args[3],args[2],args[1],args[0]};
  for(unsigned i=0;i<12;i++)write32(cs+4*i,fields[i]);
  r[4]=cs;
  if(!wnd_callback(c->proc,h,0x81,0,cs,&v)){w->live=0;return 0;}
  if(!v){r[4]=sp;w->live=0;return 1;}
  if(!wnd_callback(c->proc,h,1,0,cs,&v)){w->live=0;return 0;}
  if(v==UINT32_MAX){if(!wnd_callback(c->proc,h,0x82,0,0,&v)){w->live=0;return 0;}r[4]=sp;w->live=0;return 1;}
  r[4]=sp;
  *ret=h;report("Virtual window created: %08x %dx%d (no renderer)\n",h,ww,hh);return 1;
 }
 if(eqi(n,"DefWindowProcA")){*argc=4;p=arg(1);if(p==0x81){*ret=1;return 1;}if(p==1||p==2||p==0x82||p==0){return 1;}report("Default window message unsupported: %x\n",p);return 0;}
 if(eqi(n,"IsWindow")){*argc=1;*ret=window_find(arg(0))!=NULL;return 1;}
 if(eqi(n,"GetClientRect")||eqi(n,"GetWindowRect")){
  *argc=2;h=arg(0);p=arg(1);w=window_find(h);if(!w){last_error=1400;return 1;}
  int client=eqi(n,"GetClientRect");if(!ptr(p,16))return 0;write32(p,client?0:(uint32_t)w->x);write32(p+4,client?0:(uint32_t)w->y);write32(p+8,client?(uint32_t)w->w:(uint32_t)(w->x+w->w));write32(p+12,client?(uint32_t)w->h:(uint32_t)(w->y+w->h));*ret=1;return 1;
 }
 if(eqi(n,"PostMessageA")){*argc=4;h=arg(0);p=arg(1);q=arg(2);v=arg(3);if(h&&!window_find(h)){last_error=1400;return 1;}*ret=enqueue(h,p,q,v);return 1;}
 if(eqi(n,"PostQuitMessage")){*argc=1;return enqueue(0,0x12,arg(0),0);}
 if(eqi(n,"PeekMessageA")){
  *argc=5;p=arg(0);h=arg(1);uint32_t min=arg(2),max=arg(3),mode=arg(4);
  if(mode>1){report("Unsupported PeekMessage flags %x\n",mode);return 0;}
  if(h&&h!=UINT32_MAX&&!window_find(h)){last_error=1400;return 1;}
  for(unsigned i=0;i<message_count;i++){GuestMessage*m=&messages[i];if(m->msg!=0x12&&((h==UINT32_MAX?m->hwnd!=0:h&&m->hwnd!=h)||((min||max)&&(m->msg<min||m->msg>max))))continue;
   if(!ptr(p,28))return 0;
   uint32_t fields[]={m->hwnd,m->msg,m->wp,m->lp,m->time,(uint32_t)m->x,(uint32_t)m->y};
   for(unsigned j=0;j<7;j++)write32(p+4*j,fields[j]);
   if(mode){memmove(messages+i,messages+i+1,(message_count-i-1)*sizeof *messages);message_count--;}
   *ret=1;break;
  }return 1;
 }
 if(eqi(n,"TranslateMessage")){*argc=1;p=arg(0);if(!ptr(p,28))return 0;q=read32(p+4);if(q>=0x100&&q<=0x109){report("Keyboard translation unavailable\n");return 0;}return 1;}
 if(eqi(n,"DispatchMessageA")){*argc=1;p=arg(0);if(!ptr(p,28))return 0;h=read32(p);q=read32(p+4);v=read32(p+8);uint32_t lp=read32(p+12);if(!h)return 1;w=window_find(h);if(!w){last_error=1400;return 1;}return wnd_callback(w->proc,h,q,v,lp,ret);}
 return 0;
}
#define FILE_MAX 64u
#define FILE_BASE 0x30000u
#define FILE_LIMIT 1048576u
typedef struct{FILE*f;uint32_t handle;uint64_t length;} GuestFile;
static GuestFile files[FILE_MAX];static unsigned file_serial;
static const char guest_dir[]="C:\\games\\Grand Theft Auto San Andreas";
#ifdef __SWITCH__
static const char resource_dir[]="sdmc:/games/Grand Theft Auto San Andreas/";
#endif
/* No host paths, parent traversal, alternate drives, streams or device names. */
static int resource_path(const char*raw,char*out,unsigned cap){
 unsigned n=0;char normalized[512];unsigned len=0;
 for(;raw[len];len++){if(len>=sizeof normalized-1)return 0;unsigned char c=raw[len];if(c<32||c>=127)return 0;normalized[len]=c=='\\'?'/':(char)c;}
 normalized[len]=0;const char*p=normalized;
 const char prefix[]="C:/games/Grand Theft Auto San Andreas/";unsigned plen=sizeof prefix-1;
 if(len>=plen){char front[sizeof prefix];memcpy(front,p,plen);front[plen]=0;if(eqi(front,prefix))p+=plen;}
 if(*p=='/'||!*p)return 0;
 while(*p){const char*q=p;while(*q&&*q!='/')q++;unsigned k=(unsigned)(q-p);
  if(!k||p[k-1]=='.'||p[k-1]==' '||p[0]==' '||k>255)return 0;
  if((k==1&&p[0]=='.')||(k==2&&p[0]=='.'&&p[1]=='.'))return 0;
  char stem[256];unsigned j=0;for(;j<k&&p[j]!='.';j++)stem[j]=p[j];stem[j]=0;
  if(eqi(stem,"CON")||eqi(stem,"PRN")||eqi(stem,"AUX")||eqi(stem,"NUL")||((j==4)&&(stem[3]>='1'&&stem[3]<='9')&&(((stem[0]=='C'||stem[0]=='c')&&(stem[1]=='O'||stem[1]=='o')&&(stem[2]=='M'||stem[2]=='m'))||((stem[0]=='L'||stem[0]=='l')&&(stem[1]=='P'||stem[1]=='p')&&(stem[2]=='T'||stem[2]=='t')))))return 0;
  for(j=0;j<k;j++){unsigned char c=p[j];if(c==':'||c=='*'||c=='?'||c=='"'||c=='<'||c=='>'||c=='|')return 0;}
  if(n+k+1>=cap)return 0;
  memcpy(out+n,p,k);n+=k;if(!*q)break;out[n++]='/';p=q+1;if(!*p)return 0;
 }
 out[n]=0;return n!=0;
}
static GuestFile* file_find(uint32_t h){for(unsigned i=0;i<FILE_MAX;i++)if(files[i].f&&files[i].handle==h)return &files[i];return NULL;}
static uint32_t file_adopt(FILE*f){if(!f)return UINT32_MAX;unsigned i;for(i=0;i<FILE_MAX&&files[i].f;i++){}
 if(i==FILE_MAX||file_serial>=0xffff){fclose(f);last_error=4;return UINT32_MAX;}
 if(fseek(f,0,SEEK_END)){fclose(f);last_error=30;return UINT32_MAX;}long end=ftell(f);
 if(end<0||fseek(f,0,SEEK_SET)){fclose(f);last_error=30;return UINT32_MAX;}
 uint32_t h=FILE_BASE+(++file_serial);files[i]=(GuestFile){f,h,(uint64_t)end};return h;
}
static FILE* resource_open(const char*relative){
#ifdef __SWITCH__
 char full[768];int n=snprintf(full,sizeof full,"%s%s",resource_dir,relative);
 if(n<0||(unsigned)n>=sizeof full){last_error=206;return NULL;}
 FILE*f=fopen(full,"rb");if(!f)last_error=errno==EACCES?5:2;return f;
#else
 (void)relative;last_error=2;return NULL; /* host resource mount deliberately disabled */
#endif
}
static uint32_t file_open_guest(uint32_t name,unsigned wide,uint32_t access,uint32_t share,uint32_t security,uint32_t disposition,uint32_t flags,uint32_t tmpl){
 char raw[512],path[512];
 if(access!=0x80000000u||disposition!=3||security||tmpl||(flags&~0x08000080u)||(share&~7u)){last_error=5;return UINT32_MAX;}
 if(!guest_ascii(name,raw,sizeof raw,wide)||!resource_path(raw,path,sizeof path)){last_error=123;return UINT32_MAX;}
 return file_adopt(resource_open(path));
}
static int file_seek(GuestFile*f,int64_t off,unsigned method,uint64_t*out){
 if(method>2){last_error=87;return 0;}
 long cur=ftell(f->f);if(cur<0){last_error=30;return 0;}
 uint64_t origin=method==0?0:method==1?(uint64_t)cur:f->length;
 uint64_t target;if(off<0){uint64_t mag=(uint64_t)(-(off+1))+1;if(mag>origin){last_error=131;return 0;}target=origin-mag;}
 else{if((uint64_t)off>UINT64_MAX-origin){last_error=87;return 0;}target=origin+(uint64_t)off;}
 if(target>LONG_MAX||fseek(f->f,(long)target,SEEK_SET)){last_error=131;return 0;}
 *out=target;return 1;
}
static void close_guest_files(void){for(unsigned i=0;i<FILE_MAX;i++)if(files[i].f){fclose(files[i].f);files[i].f=NULL;}}
/* CPU reference framebuffer. COM objects and vtables live in guest memory. */
#define D3D_INVALID 0x8876086cu
#define D3D_NOTAVAILABLE 0x8876086au
#define D3D_OUTOFMEMORY 0x8007000eu
typedef struct{uint32_t obj,table,refs;} D3DObject;
static D3DObject d3d_root,d3d_device;
static uint32_t* color_buffer;
static unsigned d3d_width,d3d_height,d3d_scene,d3d_frames;
static uint32_t d3d_hash;
static void d3d_cleanup(void){free(color_buffer);color_buffer=NULL;d3d_root=(D3DObject){0};d3d_device=(D3DObject){0};d3d_width=d3d_height=d3d_scene=0;}
static int d3d_object(D3DObject*o,unsigned count,const char*const*names){
 if(!heap)return 0;
 uint32_t mem=alloc_guest(4+count*4);if(!mem)return 0;
 uint32_t table=mem+4;write32(mem,table);
 for(unsigned i=0;i<count;i++){uint32_t t=names[i]?d3d_token(names[i]):d3d_token("UnsupportedMethod");if(!t)return 0;write32(table+i*4,t);}
 if(fault)return 0;
 *o=(D3DObject){mem,table,1};return 1;
}
static int d3d_call(const char*n,unsigned*argc,uint32_t*ret){
 static const char*const root_methods[17]={[1]="RootAddRef",[2]="RootRelease",[4]="GetAdapterCount",[16]="CreateDevice"};
 static const char*const device_methods[119]={[1]="DeviceAddRef",[2]="DeviceRelease",[3]="TestCooperativeLevel",[17]="Present",[41]="BeginScene",[42]="EndScene",[43]="Clear"};
 if(!strcmp(n,"Direct3DCreate9")){
  *argc=1;if(arg(0)!=32)return 1;
  if(d3d_root.refs){if(d3d_root.refs==UINT32_MAX)return 0;d3d_root.refs++;*ret=d3d_root.obj;return 1;}
  if(!d3d_object(&d3d_root,17,root_methods))return !fault;
  *ret=d3d_root.obj;return 1;
 }
 if(!strcmp(n,"UnsupportedMethod")){report("Unsupported D3D9 COM method\n");return 0;}
 uint32_t self=arg(0);
 if(!strcmp(n,"RootAddRef")||!strcmp(n,"RootRelease")||!strcmp(n,"DeviceAddRef")||!strcmp(n,"DeviceRelease")){
  *argc=1;D3DObject*o=n[0]=='R'?&d3d_root:&d3d_device;
  if(!o->refs||self!=o->obj)return 0;
  if(strstr(n,"AddRef")){if(o->refs==UINT32_MAX)return 0;*ret=++o->refs;}
  else{if(o==&d3d_root&&o->refs==1&&d3d_device.refs){report("D3D parent reference retained by device\n");return 0;}*ret=--o->refs;if(!o->refs&&o==&d3d_device){free(color_buffer);color_buffer=NULL;d3d_scene=0;if(d3d_root.refs)d3d_root.refs--;}}
  return 1;
 }
 if(!strcmp(n,"GetAdapterCount")){*argc=1;if(self!=d3d_root.obj||!d3d_root.refs)return 0;*ret=1;return 1;}
 if(!strcmp(n,"CreateDevice")){
  *argc=7;*ret=D3D_INVALID;if(self!=d3d_root.obj||!d3d_root.refs)return 1;
  uint32_t adapter=arg(1),type=arg(2),focus=arg(3),behavior=arg(4),pp=arg(5),out=arg(6);
  uint8_t*p=ptr(pp,56);if(!p||!ptr(out,4))return 0;
  write32(out,0);if(adapter||type!=1||d3d_device.refs||d3d_root.refs==UINT32_MAX)return 1;
  unsigned w=le32(p),h=le32(p+4),fmt=le32(p+8),count=le32(p+12),ms=le32(p+16),swap=le32(p+24),hwnd=le32(p+28),windowed=le32(p+32),depth=le32(p+36);
  GuestWindow*win=window_find(hwnd?hwnd:focus);
  if(!win||!windowed||depth||ms||count>1||swap!=1||(fmt!=0&&fmt!=21&&fmt!=22)||(behavior!=0x20&&behavior!=0x40&&behavior!=0x80)){*ret=D3D_NOTAVAILABLE;return 1;}
  if(!w)w=(unsigned)win->w;
  if(!h)h=(unsigned)win->h;
  if(!w||!h||w>1920||h>1080){*ret=D3D_NOTAVAILABLE;return 1;}
  uint32_t*buf=calloc((size_t)w*h,sizeof *buf);if(!buf){*ret=D3D_OUTOFMEMORY;return 1;}
  if(!d3d_object(&d3d_device,119,device_methods)){free(buf);*ret=D3D_OUTOFMEMORY;return !fault;}
  color_buffer=buf;d3d_width=w;d3d_height=h;d3d_scene=0;d3d_root.refs++;
  write32(pp,w);write32(pp+4,h);write32(pp+8,fmt?fmt:22);write32(pp+12,1);write32(out,d3d_device.obj);
  *ret=0;report("D3D9 CPU reference device: %ux%u\n",w,h);return 1;
 }
 if(self!=d3d_device.obj||!d3d_device.refs||!color_buffer)return 0;
 *ret=D3D_INVALID;
 if(!strcmp(n,"TestCooperativeLevel")){*argc=1;*ret=0;return 1;}
 if(!strcmp(n,"BeginScene")){*argc=1;if(!d3d_scene){d3d_scene=1;*ret=0;}return 1;}
 if(!strcmp(n,"EndScene")){*argc=1;if(d3d_scene){d3d_scene=0;*ret=0;}return 1;}
 if(!strcmp(n,"Clear")){
  *argc=7;uint32_t count=arg(1),rect=arg(2),flags=arg(3),color=arg(4);
  if(count||rect||flags!=1)return 1;
  for(size_t i=0;i<(size_t)d3d_width*d3d_height;i++)color_buffer[i]=color;
  *ret=0;return 1;
 }
 if(!strcmp(n,"Present")){
  *argc=5;if(d3d_scene||arg(1)||arg(2)||arg(3)||arg(4))return 1;
  uint32_t hash=2166136261u;for(size_t i=0;i<(size_t)d3d_width*d3d_height;i++){uint32_t v=color_buffer[i];for(unsigned k=0;k<4;k++){hash^=(v>>(k*8))&255;hash*=16777619u;}}
  d3d_hash=hash;d3d_frames++;*ret=0;report("D3D9 reference frame %u hash=%08x (not displayed)\n",d3d_frames,hash);return 1;
 }
 return 0;
}
static int api_call(uint32_t target,unsigned iscall){
 if(target<APITOKEN||((target-APITOKEN)&3)||(target-APITOKEN)/4>=import_count)return -1;
 api_arg_offset=iscall?0:4;Import*x=&imports[(target-APITOKEN)/4];const char*n=x->name;unsigned argc=0;uint32_t ret=0,p,q,t;uint8_t*dst;
 if(n&&eqi(x->dll,"d3d9.dll")){if(!d3d_call(n,&argc,&ret))goto missing;goto finish;}
 if(n&&eqi(x->dll,"user32.dll")){if(!user_call(n,&argc,&ret))goto missing;goto finish;}
 if(!eqi(x->dll,"kernel32.dll")||!n)goto missing;
 if(eqi(n,"GetVersionExA")||eqi(n,"GetVersionExW")){
  argc=1;p=arg(0);q=read32(p);unsigned wide=eqi(n,"GetVersionExW");
  unsigned basic=wide?276:148,extended=wide?284:156;
  if(q!=basic&&q!=extended){last_error=122;ret=0;}else{
   dst=ptr(p,q);if(!dst)return 0;memset(dst,0,q);write32(p,q);write32(p+4,5);write32(p+8,1);write32(p+12,2600);write32(p+16,2);if(q==extended)dst[basic+6]=1;ret=1;
  }
 }else if(eqi(n,"GetVersion")){ret=0x0a280105u;}
 else if(eqi(n,"SetUnhandledExceptionFilter")){argc=1;ret=exception_filter;exception_filter=arg(0);}
 else if(eqi(n,"GetSystemTimeAsFileTime")){argc=1;p=arg(0);uint64_t ft=UINT64_C(133801632000000000)+(uint64_t)steps*100;write32(p,(uint32_t)ft);write32(p+4,(uint32_t)(ft>>32));}
 else if(eqi(n,"GetTickCount")){ret=steps/100;}
 else if(eqi(n,"QueryPerformanceCounter")||eqi(n,"QueryPerformanceFrequency")){argc=1;p=arg(0);uint64_t v=eqi(n,"QueryPerformanceFrequency")?UINT64_C(1000000):(uint64_t)steps*10;write32(p,(uint32_t)v);write32(p+4,(uint32_t)(v>>32));ret=1;}
 else if(eqi(n,"GetLastError")){ret=last_error;}
 else if(eqi(n,"SetLastError")){argc=1;last_error=arg(0);}
 else if(eqi(n,"GetCurrentProcessId")||eqi(n,"GetCurrentThreadId")){ret=1;}
 else if(eqi(n,"GetCurrentProcess")){ret=0xffffffffu;}
 else if(eqi(n,"GetCurrentThread")){ret=0xfffffffeu;}
 else if(eqi(n,"GetProcessHeap")){ret=HEAPBASE;}
 else if(eqi(n,"GetModuleHandleA")||eqi(n,"GetModuleHandleW")||eqi(n,"LoadLibraryA")||eqi(n,"LoadLibraryW")){
  char name[128]={0};unsigned load=eqi(n,"LoadLibraryA")||eqi(n,"LoadLibraryW"),wide=eqi(n,"GetModuleHandleW")||eqi(n,"LoadLibraryW");argc=1;p=arg(0);
  if(!p&&!load)ret=base;
  else if(guest_ascii(p,name,sizeof name,wide)){
   if(eqi(name,"kernel32")||eqi(name,"kernel32.dll")){
   if(load&&kernel_refs==UINT32_MAX){last_error=8;}else{if(load)kernel_refs++;ret=KERNEL32_HANDLE;}
  }else if(eqi(name,"user32")||eqi(name,"user32.dll")){if(load&&user_refs==UINT32_MAX)last_error=8;else{if(load)user_refs++;ret=USER32_HANDLE;}}else if(eqi(name,"d3d9")||eqi(name,"d3d9.dll")){if(load&&d3d_refs==UINT32_MAX)last_error=8;else{if(load)d3d_refs++;ret=D3D9_HANDLE;}}else last_error=126;
  }else last_error=126;
 }else if(eqi(n,"GetProcAddress")){
  char name[128];argc=2;p=arg(0);q=arg(1);
  if(p!=KERNEL32_HANDLE&&p!=USER32_HANDLE&&p!=D3D9_HANDLE){last_error=6;}else if(q<=65535||!guest_ascii(q,name,sizeof name,0)){last_error=127;}else{ret=p==KERNEL32_HANDLE?kernel_export(name):p==USER32_HANDLE?user_export(name):!strcmp(name,"Direct3DCreate9")?d3d_token("Direct3DCreate9"):0;if(!ret)last_error=127;}
 }else if(eqi(n,"FreeLibrary")){argc=1;p=arg(0);if(p==KERNEL32_HANDLE&&kernel_refs>1){kernel_refs--;ret=1;}else if(p==USER32_HANDLE&&user_refs>1){user_refs--;ret=1;}else if(p==D3D9_HANDLE&&d3d_refs>1){d3d_refs--;ret=1;}else last_error=6;}
 else if(eqi(n,"GetCommandLineA")){static const char cmd[]="\"C:\\games\\Grand Theft Auto San Andreas\\gta_sa.exe\"";ret=HEAPBASE+0x100;copyguest(ret,cmd,sizeof cmd);}
 else if(eqi(n,"GetCommandLineW")){static const char cmd[]="\"C:\\games\\Grand Theft Auto San Andreas\\gta_sa.exe\"";ret=HEAPBASE+0x200;dst=ptr(ret,2*sizeof cmd);if(!dst)return 0;for(unsigned i=0;i<sizeof cmd;i++){dst[2*i]=cmd[i];dst[2*i+1]=0;}}
 else if(eqi(n,"GetSystemInfo")){argc=1;p=arg(0);dst=ptr(p,36);if(!dst)return 0;memset(dst,0,36);write32(p+4,4096);write32(p+8,0x10000);write32(p+12,0x7ffeffff);write32(p+16,1);write32(p+20,1);write32(p+24,586);write32(p+28,65536);dst[32]=6;}
 else if(eqi(n,"HeapCreate")){argc=3;p=arg(0);q=arg(1);t=arg(2);if((p&0x00040000u)||q>HEAPSIZE||(t&&t<q)){last_error=87;}else{for(unsigned i=1;i<MAXHEAPS;i++)if(!heap_live[i]){heap_live[i]=1;ret=HEAPBASE+4*i;break;}if(!ret)last_error=8;}}
 else if(eqi(n,"HeapDestroy")){argc=1;p=arg(0);int idx=heap_index(p);if(idx<=0){last_error=6;}else{for(unsigned i=0;i<block_count;i++)if(blocks[i].owner==p)blocks[i].live=0;heap_live[idx]=0;ret=1;}}
 else if(eqi(n,"HeapAlloc")){argc=3;ret=heap_alloc(arg(0),arg(1),arg(2));}
 else if(eqi(n,"HeapFree")||eqi(n,"HeapSize")||eqi(n,"HeapValidate")){argc=3;p=arg(0);q=arg(2);HeapBlock*b=find_block(p,q);if(eqi(n,"HeapValidate")){ret=heap_index(p)>=0&&(!q||b!=NULL);}else if(!b||heap_index(p)<0){last_error=6;ret=eqi(n,"HeapSize")?UINT32_MAX:0;}else if(eqi(n,"HeapSize"))ret=b->requested;else{b->live=0;ret=1;}}
 else if(eqi(n,"HeapReAlloc")){argc=4;ret=heap_realloc(arg(0),arg(1),arg(2),arg(3));}
 else if(eqi(n,"GetStartupInfoA")||eqi(n,"GetStartupInfoW")){argc=1;p=arg(0);dst=ptr(p,68);if(!dst)return 0;memset(dst,0,68);write32(p,68);write32(p+56,0xffffffffu);write32(p+60,0xffffffffu);write32(p+64,0xffffffffu);}
 else if(eqi(n,"GetEnvironmentStringsA")||eqi(n,"GetEnvironmentStringsW")){ret=HEAPBASE+0x400;dst=ptr(ret,4);if(!dst)return 0;memset(dst,0,4);}
 else if(eqi(n,"FreeEnvironmentStringsA")||eqi(n,"FreeEnvironmentStringsW")){argc=1;ret=arg(0)==HEAPBASE+0x400;if(!ret)last_error=87;}
 else if(eqi(n,"InitializeCriticalSection")||eqi(n,"InitializeCriticalSectionAndSpinCount")){
  argc=eqi(n,"InitializeCriticalSection")?1:2;p=arg(0);dst=ptr(p,24);if(!dst)return 0;Critical*c=critical_find(p,1);if(!c){report("Critical section capacity exceeded\n");return 0;}c->depth=0;memset(dst,0,24);if(argc==2)write32(p+20,arg(1));if(!critical_write(c))return 0;ret=argc==2;
 }else if(eqi(n,"EnterCriticalSection")||eqi(n,"TryEnterCriticalSection")||eqi(n,"LeaveCriticalSection")||eqi(n,"DeleteCriticalSection")){
  argc=1;p=arg(0);Critical*c=critical_find(p,0);if(!c){report("Invalid guest critical section %08x\n",p);return 0;}
  if(eqi(n,"DeleteCriticalSection")){if(c->depth){report("Deleting held guest critical section\n");return 0;}c->active=0;}
  else{if(eqi(n,"LeaveCriticalSection")){if(!c->depth){report("Guest critical section not held\n");return 0;}c->depth--;}else{if(c->depth==UINT32_MAX){report("Guest critical recursion overflow\n");return 0;}c->depth++;ret=eqi(n,"TryEnterCriticalSection");}if(!critical_write(c))return 0;}
 }else if(eqi(n,"TlsAlloc")){ret=UINT32_MAX;for(unsigned i=0;i<64;i++)if(!(tls_used&(UINT64_C(1)<<i))){tls_used|=UINT64_C(1)<<i;tls_values[i]=0;ret=i;break;}if(ret==UINT32_MAX)last_error=8;}
 else if(eqi(n,"TlsFree")||eqi(n,"TlsGetValue")||eqi(n,"TlsSetValue")){
  argc=eqi(n,"TlsSetValue")?2:1;p=arg(0);if(p>=64||!(tls_used&(UINT64_C(1)<<p))){last_error=87;ret=0;}
  else if(eqi(n,"TlsFree")){tls_used&=~(UINT64_C(1)<<p);tls_values[p]=0;ret=1;}
  else if(eqi(n,"TlsSetValue")){tls_values[p]=arg(1);ret=1;}else{last_error=0;ret=tls_values[p];}
 }else if(eqi(n,"WideCharToMultiByte")||eqi(n,"MultiByteToWideChar")){
  unsigned wide=eqi(n,"WideCharToMultiByte"),used=0,fallback='?';argc=wide?8:6;p=arg(0);q=arg(1);
  if(p!=0&&p!=1252){report("Unsupported guest code page %u\n",p);return 0;}
  if(q&&(wide||q!=1)){report("Unsupported conversion flags %08x\n",q);return 0;}
  if(wide&&arg(6)){uint8_t*d=ptr(arg(6),1);if(!d)return 0;fallback=*d;}
  ret=convert1252(wide,arg(2),(int32_t)arg(3),arg(4),(int32_t)arg(5),fallback,&used);
  if(wide&&arg(7)&&!fault)write32(arg(7),used);
 }else if(eqi(n,"SetHandleCount")){argc=1;ret=arg(0);}
 else if(eqi(n,"GetModuleFileNameA")||eqi(n,"GetModuleFileNameW")){
  static const char path[]="C:\\games\\Grand Theft Auto San Andreas\\gta_sa.exe";
  argc=3;p=arg(0);q=arg(1);t=arg(2);unsigned wide=eqi(n,"GetModuleFileNameW"),len=sizeof path-1;
  if(p&&p!=base){last_error=6;}else if(!t){last_error=122;}else{unsigned ncopy=t<=len?t:len+1;dst=ptr(q,ncopy*(wide?2:1));if(!dst)return 0;for(unsigned i=0;i<ncopy;i++){if(wide){dst[i*2]=(uint8_t)path[i];dst[i*2+1]=0;}else dst[i]=(uint8_t)path[i];}ret=t<=len?t:len;if(t<=len)last_error=122;}
 }else if(eqi(n,"lstrlenA")||eqi(n,"lstrlenW")){
  argc=1;p=arg(0);unsigned w=eqi(n,"lstrlenW")?2:1;if(p){for(uint32_t i=0;i<65536;i++){dst=ptr(p+i*w,w);if(!dst)return 0;if(!(w==1?dst[0]:le16(dst))){ret=i;break;}if(i==65535){report("Guest string limit\n");return 0;}}}
 }else if(eqi(n,"GetStdHandle")){argc=1;p=arg(0);if(p==0xfffffff6u||p==0xfffffff5u||p==0xfffffff4u)ret=std_handles[0xfffffff6u-p];else{last_error=87;ret=UINT32_MAX;}}
 else if(eqi(n,"SetStdHandle")){argc=2;p=arg(0);q=arg(1);if(p==0xfffffff6u||p==0xfffffff5u||p==0xfffffff4u){std_handles[0xfffffff6u-p]=q;ret=1;}else last_error=87;}
 else if(eqi(n,"CreateFileA")||eqi(n,"CreateFileW")){argc=7;uint32_t v[7];for(unsigned i=0;i<7;i++)v[i]=arg(i);if(fault)return 0;ret=file_open_guest(v[0],eqi(n,"CreateFileW"),v[1],v[2],v[3],v[4],v[5],v[6]);}
 else if(eqi(n,"GetFileAttributesA")||eqi(n,"GetFileAttributesW")){argc=1;char raw[512],path[512];ret=UINT32_MAX;if(guest_ascii(arg(0),raw,sizeof raw,eqi(n,"GetFileAttributesW"))&&resource_path(raw,path,sizeof path)){FILE*f=resource_open(path);if(f){fclose(f);ret=0x80;}}else last_error=123;}
 else if(eqi(n,"GetCurrentDirectoryA")||eqi(n,"GetCurrentDirectoryW")){argc=2;unsigned wide=eqi(n,"GetCurrentDirectoryW"),n=sizeof guest_dir;p=arg(0);q=arg(1);if(p<n)ret=n;else{dst=ptr(q,n*(wide?2:1));if(!dst)return 0;for(unsigned i=0;i<n;i++){dst[i*(wide?2:1)]=(uint8_t)guest_dir[i];if(wide)dst[2*i+1]=0;}ret=n-1;}}
 else if(eqi(n,"GetFileSize")||eqi(n,"GetFileSizeEx")){argc=2;p=arg(0);q=arg(1);GuestFile*f=file_find(p);unsigned ex=eqi(n,"GetFileSizeEx");if(!f){last_error=6;ret=ex?0:UINT32_MAX;}else if(ex){write32(q,(uint32_t)f->length);write32(q+4,(uint32_t)(f->length>>32));ret=1;}else{if(q)write32(q,(uint32_t)(f->length>>32));ret=(uint32_t)f->length;last_error=0;}}
 else if(eqi(n,"SetFilePointer")||eqi(n,"SetFilePointerEx")){argc=4;p=arg(0);q=arg(1);t=arg(2);uint64_t pos=0;GuestFile*f=file_find(p);unsigned ex=eqi(n,"SetFilePointerEx");uint32_t high=ex?t:t?read32(t):((int32_t)q<0?UINT32_MAX:0),out=ex?arg(3):t,method=ex?arg(4):arg(3);if(ex)argc=5;int64_t off=(int64_t)(((uint64_t)high<<32)|q);if(!f){last_error=6;ret=ex?0:UINT32_MAX;}else if(fault||!file_seek(f,off,method,&pos)){ret=ex?0:UINT32_MAX;}else{if(out){if(ex){write32(out,(uint32_t)pos);write32(out+4,(uint32_t)(pos>>32));}else write32(out,(uint32_t)(pos>>32));}ret=ex?1:(uint32_t)pos;last_error=0;}}
 else if(eqi(n,"GetFileType")){argc=1;p=arg(0);if(file_find(p))ret=1;else if(p>=0x10001u&&p<=0x10003u&&std_live[p-0x10001u])ret=2;else last_error=6;}
 else if(eqi(n,"CloseHandle")){argc=1;p=arg(0);GuestFile*f=file_find(p);if(f){int status=fclose(f->f);f->f=NULL;ret=status==0;if(!ret)last_error=30;}else if(p>=0x10001u&&p<=0x10003u&&std_live[p-0x10001u]){std_live[p-0x10001u]=0;ret=1;}else last_error=6;}
 else if(eqi(n,"WriteFile")||eqi(n,"ReadFile")){argc=5;p=arg(0);q=arg(1);t=arg(2);uint32_t done=arg(3),overlap=arg(4);
  if(overlap){report("Asynchronous file IO unavailable\n");return 0;}
  if(done)write32(done,0);
  if(t>FILE_LIMIT){report("Guest IO request too large\n");return 0;}
  GuestFile*f=file_find(p);if(f){if(eqi(n,"WriteFile")){last_error=5;}else{dst=t?ptr(q,t):NULL;if(t&&!dst)return 0;if(fault)return 0;size_t got=t?fread(dst,1,t,f->f):0;if(done)write32(done,(uint32_t)got);if(ferror(f->f)){last_error=30;clearerr(f->f);}else ret=1;}}else
  if(eqi(n,"WriteFile")&&(p==0x10002u||p==0x10003u)&&std_live[p-0x10001u]){dst=t?ptr(q,t):NULL;if(t&&!dst)return 0;if(t){report("Guest console wrote %u bytes\n",t);if(logfile)fwrite(dst,1,t,logfile);}if(done)write32(done,t);ret=1;}
  else if(eqi(n,"ReadFile")&&p==0x10001u&&std_live[0]){if(t&&!ptr(q,t))return 0;ret=1;}else last_error=6;
 }else if(eqi(n,"GetConsoleMode")){argc=2;p=arg(0);q=arg(1);if(p>=0x10001u&&p<=0x10003u&&std_live[p-0x10001u]){write32(q,p==0x10001u?7:3);ret=1;}else last_error=6;}
 else if(eqi(n,"LCMapStringW")||eqi(n,"LCMapStringA")){
  argc=6;unsigned wide=eqi(n,"LCMapStringW"),w=wide?2:1;uint32_t mode=arg(1),src=arg(2),out=arg(4);int32_t len=(int32_t)arg(3),cap=(int32_t)arg(5);
  if(mode!=0x100&&mode!=0x200){report("Unsupported LCMapString flags %08x\n",mode);return 0;}
  if(len==-1){unsigned i;for(i=0;i<65536;i++){uint8_t*c=ptr(src+i*w,w);if(!c)return 0;if(!(wide?le16(c):*c))break;}len=i<65536?(int32_t)(i+1):0;}
  if(len<=0||len>65536||cap<0){last_error=87;}else if(cap&&cap<len){last_error=122;}else{
   uint8_t*in=ptr(src,(unsigned)len*w);dst=cap?ptr(out,(unsigned)len*w):NULL;if(!in||(cap&&!dst))return 0;
   for(int32_t i=0;i<len;i++){unsigned u=wide?le16(in+2*i):cp1252_decode(in[i]);u=mode==0x100?lower1252(u):upper1252(u);if(dst){if(wide){dst[2*i]=u;dst[2*i+1]=u>>8;}else{unsigned used=0;dst[i]=cp1252_encode(u,in[i],&used);}}}ret=len;
  }
 }else if(eqi(n,"GetStringTypeW")||eqi(n,"GetStringTypeA")){
  unsigned wide=eqi(n,"GetStringTypeW");argc=wide?4:5;unsigned shift=wide?0:1;uint32_t kind=arg(shift),src=arg(shift+1),out=arg(shift+3);int32_t len=(int32_t)arg(shift+2);unsigned w=wide?2:1;
  if(kind!=1){report("Unsupported string type %u\n",kind);return 0;}
  if(len==-1){len=0;while(len<65536){uint8_t*c=ptr(src+(unsigned)len*w,w);if(!c)return 0;len++;if(!(wide?le16(c):*c))break;}}
  if(len<=0||len>65536){last_error=87;}else{uint8_t*in=ptr(src,(unsigned)len*w);dst=ptr(out,(unsigned)len*2);if(!in||!dst)return 0;for(int32_t i=0;i<len;i++){unsigned u=wide?le16(in+2*i):cp1252_decode(in[i]);unsigned f=type1252(u);dst[2*i]=f;dst[2*i+1]=f>>8;}ret=1;}
 }else if(eqi(n,"GetCPInfo")){argc=2;p=arg(0);q=arg(1);if(p==0||p==1252||p==437||p==1){dst=ptr(q,20);if(!dst)return 0;memset(dst,0,20);write32(q,1);dst[4]='?';ret=1;}else last_error=87;}
 else if(eqi(n,"IsValidCodePage")){argc=1;p=arg(0);ret=p==1252||p==437;}
 else if(eqi(n,"GetThreadLocale")||eqi(n,"GetUserDefaultLCID")||eqi(n,"GetSystemDefaultLCID")){ret=0x409;}
 else if(eqi(n,"GetUserDefaultLangID")||eqi(n,"GetSystemDefaultLangID")){ret=0x409;}
 else if(eqi(n,"GetACP")||eqi(n,"GetOEMCP")){ret=eqi(n,"GetACP")?1252:437;}
 else if(eqi(n,"IsDebuggerPresent")){ret=0;}
 else goto missing;
 finish:
 if(fault)return 0;
 if(!iscall){uint32_t next=pop();if(fault)return 0;ip=next;}
 r[4]=ga(r[4],argc*4);r[0]=ret;api_calls++;
 report("API %s!%s -> %08x\n",x->dll,n,ret);return 1;
 missing:if(n)report("Unresolved import %s!%s\n",x->dll,n);else report("Unresolved import %s ordinal %u\n",x->dll,x->ordinal);return 0;
}
static int fp_has(unsigned i){return (fp_mask>>( (fp_top+i)&7))&1;}
static double fp_get(unsigned i){return fp[(fp_top+i)&7];}
static void fp_put(unsigned i,double v){unsigned k=(fp_top+i)&7;fp[k]=v;fp_mask|=1u<<k;}
static int fp_push(double v){unsigned k=(fp_top+7)&7;if(fp_mask&(1u<<k))return 0;fp_top=k;fp_put(0,v);return 1;}
static int fp_pop(void){if(!fp_has(0))return 0;fp_mask&=~(1u<<fp_top);fp_top=(fp_top+1)&7;return 1;}
static void fp_compare(double a,double b){fp_status&=~0x4500u;if(a!=a||b!=b)fp_status|=0x4500;else if(a<b)fp_status|=0x100;else if(a==b)fp_status|=0x4000;}
static uint16_t fp_sw(void){return (fp_status&~0x3800u)|(fp_top<<11);}
static int fp_arith(unsigned g,double a,double b,double*out){switch(g){case 0:*out=a+b;break;case 1:*out=a*b;break;case 4:*out=a-b;break;case 5:*out=b-a;break;case 6:if(b==0)return 0;*out=a/b;break;case 7:if(a==0)return 0;*out=b/a;break;default:return 0;}return 1;}
static int fp_step(unsigned op,unsigned fs){unsigned m=byte(),g=m>>3&7,k=m&7;double v=0,z=0;Operand o;uint8_t*p;
 if(fault)return 0;
 if(m>=192){
  if(op==0xdf&&m==0xe0){r[0]=(r[0]&0xffff0000u)|fp_sw();return 1;}
  if(op==0xdb&&m==0xe3){fp_top=fp_mask=fp_status=0;fp_control=0x37f;return 1;}
  if(op==0xdb&&m==0xe2){fp_status&=~0x80ffu;return 1;}
  if(op==0xd9&&m>=0xe8&&m<=0xee){static const double constants[]={1,3.321928094887362,1.4426950408889634,3.141592653589793,0.3010299956639812,0.6931471805599453,0};return fp_push(constants[m-0xe8]);}
  if(op==0xd9&&g==0){return fp_has(k)&&fp_push(fp_get(k));}
  if(op==0xdd&&g==0){fp_mask&=~(1u<<((fp_top+k)&7));return 1;}
  if(!fp_has(0))return 0;
  if(op==0xd9&&m==0xe0){fp_put(0,-fp_get(0));return 1;}
  if(op==0xd9&&m==0xe1){v=fp_get(0);fp_put(0,v<0?-v:v);return 1;}
  if(op==0xd9&&m==0xe4){fp_compare(fp_get(0),0);return 1;}
  if(op==0xd9&&g==1){if(!fp_has(k))return 0;v=fp_get(k);fp_put(k,fp_get(0));fp_put(0,v);return 1;}
  if(op==0xdd&&(g==2||g==3)){fp_put(k,fp_get(0));return g==2||fp_pop();}
  if(!fp_has(k))return 0;
  if(op==0xd8){if(g==2||g==3){fp_compare(fp_get(0),fp_get(k));return g==2||fp_pop();}if(!fp_arith(g,fp_get(0),fp_get(k),&z))return 0;fp_put(0,z);return 1;}
  if(op==0xdc||op==0xde){if(op==0xde&&m==0xd9){fp_compare(fp_get(0),fp_get(1));return fp_pop()&&fp_pop();}if(g==2||g==3)return 0;unsigned gg=g>=4?g^1:g;if(!fp_arith(gg,fp_get(k),fp_get(0),&z))return 0;fp_put(k,z);return op==0xdc||fp_pop();}
  if(op==0xdd&&(g==4||g==5)){fp_compare(fp_get(0),fp_get(k));return g==4||fp_pop();}
  return 0;
 }
 o=decode(m,fs);if(fault)return 0;
 if(op==0xd9&&(g==5||g==7)){p=ptr(o.addr,2);if(!p)return 0;if(g==5)fp_control=le16(p);else{p[0]=fp_control;p[1]=fp_control>>8;}return 1;}
 if(op==0xdd&&g==7){p=ptr(o.addr,2);if(!p)return 0;uint16_t sw=fp_sw();p[0]=sw;p[1]=sw>>8;return 1;}
 if(op==0xd9||op==0xdd){unsigned w=op==0xd9?4:8;if(g!=0&&g!=2&&g!=3)return 0;p=ptr(o.addr,w);if(!p)return 0;if(g==0){if(w==4){float x;memcpy(&x,p,4);v=x;}else memcpy(&v,p,8);return fp_push(v);}if(!fp_has(0))return 0;v=fp_get(0);if(w==4){float x=(float)v;memcpy(p,&x,4);}else memcpy(p,&v,8);return g==2||fp_pop();}
 if(op==0xdb||op==0xdf){unsigned w=op==0xdb?4:(g==5||g==7?8:2);if(g!=0&&!(op==0xdf&&g==5))return 0;p=ptr(o.addr,w);if(!p)return 0;if(w==2)v=(int16_t)le16(p);else if(w==4)v=(int32_t)le32(p);else{int64_t x;memcpy(&x,p,8);v=(double)x;}return fp_push(v);}
 if(op==0xd8||op==0xdc||op==0xda||op==0xde){unsigned w=op==0xdc?8:op==0xde?2:4;p=ptr(o.addr,w);if(!p||!fp_has(0))return 0;if(op==0xd8){float x;memcpy(&x,p,4);v=x;}else if(op==0xdc)memcpy(&v,p,8);else v=w==2?(int16_t)le16(p):(int32_t)le32(p);if(g==2||g==3){fp_compare(fp_get(0),v);return g==2||fp_pop();}if(!fp_arith(g,fp_get(0),v,&z))return 0;fp_put(0,z);return 1;}
 return 0;
}
static int step(void){uint32_t start=ip,v,a,b;unsigned op=byte(),m,g,fs=0,os16=0,repeat=0;Operand o;if(fault)return 0;for(unsigned p=0;p<4&&(op==0x64||op==0x66||op==0xf2||op==0xf3);p++){if(op==0x64)fs=1;else if(op==0x66)os16=1;else repeat=op;op=byte();if(fault)return 0;}if(op>=0xa4&&op<=0xaf&&(op<0xa8||op>0xa9)){
 unsigned width=(op&1)?(os16?2:4):1;uint32_t count=repeat?r[1]:1;
 if(count>1048576u){report("String operation limit at %08x count=%u\n",start,count);return 0;}
 for(uint32_t i=0;i<count;i++){
  unsigned src=(op==0xa4||op==0xa5||op==0xa6||op==0xa7||op==0xac||op==0xad),dest=(op==0xa4||op==0xa5||op==0xa6||op==0xa7||op==0xaa||op==0xab||op==0xae||op==0xaf);
  uint8_t*sp=src?ptr(fs?ga(r[6],TEBBASE):r[6],width):NULL,*dp=dest?ptr(r[7],width):NULL;if(fault)break;
  uint32_t x=src?(width==1?sp[0]:width==2?le16(sp):le32(sp)):r[0],y=dest?(width==1?dp[0]:width==2?le16(dp):le32(dp)):0;
  if(op==0xa4||op==0xa5||op==0xaa||op==0xab){for(unsigned j=0;j<width;j++)dp[j]=(uint8_t)(x>>(8*j));}
  else if(op==0xac||op==0xad){uint32_t mask=width==1?255:width==2?65535:UINT32_MAX;r[0]=(r[0]&~mask)|(x&mask);}
  else if(width==4)(void)alu(7,x,y);else if(width==2)(void)alu16(7,x,y);else{uint32_t a8=x&255,b8=y&255,v8=gs(a8,b8)&255;commonflags(v8);sflag=v8>>7;cflag=a8<b8;oflag=((a8^b8)&(a8^v8))>>7&1;aflag=(a8^b8^v8)>>4&1;}
  if(src){r[6]=dflag?gs(r[6],width):ga(r[6],width);}
  if(dest)r[7]=dflag?gs(r[7],width):ga(r[7],width);
  if(repeat){r[1]=gs(r[1],1);if((op==0xa6||op==0xa7||op==0xae||op==0xaf)&&((repeat==0xf3&&!zflag)||(repeat==0xf2&&zflag)))break;}
 }
 goto completed;
 }
 if(repeat==0xf3&&op==0x90&&!os16&&!fs)goto completed;
 if(repeat)goto unsupported;
 if(op==0xf0&&!os16&&!fs){
  unsigned locked=byte(),mm=byte(),group=mm>>3&7;Operand dst=decode(mm,0);
  if(fault||dst.reg||(locked!=0xfe&&locked!=0xff)||group>1)goto unsupported;
  unsigned old=cflag;
  if(locked==0xfe)put8(dst,alu8(group?5:0,get8(dst),1));
  else put(dst,alu(group?5:0,get(dst),1));
  cflag=old;goto completed;
 }
 if(op>=0xd8&&op<=0xdf&&!os16){if(!fp_step(op,fs))goto unsupported;goto completed;}
 if(op==0x9b&&!os16)goto completed;
 if(os16){if(!step16(op,fs))goto unsupported;goto completed;}
 if(op>=0x50&&op<=0x57&&!fs){v=r[op-0x50];push(v);}
 else if(op>=0x58&&op<=0x5f&&!fs){v=pop();r[op-0x58]=v;}
 else if(op>=0xb8&&op<=0xbf&&!fs)r[op-0xb8]=imm();
 else if(op>=0x70&&op<=0x7f){v=(uint32_t)(int32_t)(int8_t)byte();if(condition(op&15))ip=ga(ip,v);}
 else if(op>=0x40&&op<=0x4f){unsigned old=cflag;g=op&7;r[g]=alu(op<0x48?0:5,r[g],1);cflag=old;}
 else if(op>=0x91&&op<=0x97&&!fs){g=op&7;v=r[0];r[0]=r[g];r[g]=v;}
 else if(op>=0xb0&&op<=0xb7){o=(Operand){1,op&7,0};put8(o,byte());}
 else switch(op){
 case 0x90:if(fs)goto unsupported;break;case 0xfc:dflag=0;break;case 0xfd:dflag=1;break;case 0xf8:cflag=0;break;case 0xf9:cflag=1;break;
 case 0x60:v=r[4];for(unsigned j=0;j<8;j++)push(j==4?v:r[j]);break;
 case 0x61:for(int j=7;j>=0;j--){v=pop();if(j!=4)r[j]=v;}break;
 case 0xe0:case 0xe1:case 0xe2:case 0xe3:v=(uint32_t)(int32_t)(int8_t)byte();if(op!=0xe3)r[1]=gs(r[1],1);if(op==0xe3?!r[1]:r[1]&&(op==0xe2||(op==0xe1?zflag:!zflag)))ip=ga(ip,v);break;
 case 0x68:v=imm();push(v);break;case 0x6a:v=(uint32_t)(int32_t)(int8_t)byte();push(v);break;
 case 0xe8:v=imm();push(ip);ip=ga(ip,v);break;case 0xe9:v=imm();ip=ga(ip,v);break;case 0xeb:v=(uint32_t)(int32_t)(int8_t)byte();ip=ga(ip,v);break;
 case 0x9c:v=2|cflag|(pflag<<2)|(aflag<<4)|(zflag<<6)|(sflag<<7)|(dflag<<10)|(oflag<<11)|0x200;push(v);break;
 case 0x9d:v=pop();cflag=v&1;pflag=v>>2&1;aflag=v>>4&1;zflag=v>>6&1;sflag=v>>7&1;dflag=v>>10&1;oflag=v>>11&1;break;
 case 0x9e:v=r[0]>>8;cflag=v&1;pflag=v>>2&1;aflag=v>>4&1;zflag=v>>6&1;sflag=v>>7&1;break;
 case 0x9f:v=2|cflag|(pflag<<2)|(aflag<<4)|(zflag<<6)|(sflag<<7);put8((Operand){1,4,0},v);break;
 case 0xc2:v=imm16();ip=pop();r[4]=ga(r[4],v);break;case 0xc3:ip=pop();break;case 0xc9:r[4]=r[5];r[5]=pop();break;
 case 0xa0:v=imm();put8((Operand){1,0,0},get8((Operand){0,0,fs?ga(v,TEBBASE):v}));break;
 case 0xa2:v=imm();put8((Operand){0,0,fs?ga(v,TEBBASE):v},r[0]);break;
 case 0xa1:v=imm();r[0]=read32(fs?ga(v,TEBBASE):v);break;case 0xa3:v=imm();write32(fs?ga(v,TEBBASE):v,r[0]);break;
 case 0x89:case 0x8b:case 0x8d:case 0x31:case 0x33:case 0x2b:case 0x29:case 0x85:case 0x01:case 0x03:case 0x39:case 0x3b:case 0x21:case 0x23:case 0x09:case 0x0b:case 0x11:case 0x13:case 0x19:case 0x1b:
 m=byte();g=m>>3&7;o=decode(m,op==0x8d?0:fs);if(fault)break;
 if(op==0x89)put(o,r[g]);else if(op==0x8b)r[g]=get(o);else if(op==0x8d){if(o.reg)goto unsupported;r[g]=o.addr;}
 else if(op==0x85){(void)alu(4,get(o),r[g]);}
 else{unsigned group=(op>>3)&7;unsigned dest=op&2;if(dest){v=alu(group,r[g],get(o));if(group!=7)r[g]=v;}else{v=alu(group,get(o),r[g]);if(group!=7)put(o,v);}}
 break;
 case 0x86:m=byte();g=m>>3&7;o=decode(m,fs);{Operand reg={1,g,0};v=get8(o);put8(o,get8(reg));put8(reg,v);}break;
 case 0x87:m=byte();g=m>>3&7;o=decode(m,fs);v=get(o);put(o,r[g]);r[g]=v;break;
 case 0xc7:m=byte();if((m>>3&7)!=0)goto unsupported;o=decode(m,fs);v=imm();put(o,v);break;
 case 0x81:case 0x83:m=byte();g=m>>3&7;o=decode(m,fs);b=op==0x81?imm():(uint32_t)(int32_t)(int8_t)byte();a=get(o);v=alu(g,a,b);if(g!=7)put(o,v);break;
 case 0x05:case 0x0d:case 0x15:case 0x1d:case 0x25:case 0x2d:case 0x35:case 0x3d:g=op>>3&7;v=imm();v=alu(g,r[0],v);if(g!=7)r[0]=v;break;
 case 0xa9:v=imm();(void)alu(4,r[0],v);break;
 case 0x80:m=byte();g=m>>3&7;o=decode(m,fs);b=byte();v=alu8(g,get8(o),b);if(g!=7)put8(o,v);break;
 case 0x00:case 0x02:case 0x08:case 0x0a:case 0x10:case 0x12:case 0x18:case 0x1a:case 0x20:case 0x22:case 0x28:case 0x2a:case 0x30:case 0x32:case 0x38:case 0x3a:case 0x84:
 m=byte();g=m>>3&7;o=decode(m,fs);{Operand reg={1,g,0};if(op==0x84)(void)alu8(4,get8(o),get8(reg));else{unsigned group=op>>3&7;Operand dest=(op&2)?reg:o;v=alu8(group,get8(dest),(op&2)?get8(o):get8(reg));if(group!=7)put8(dest,v);}}break;
 case 0x04:case 0x0c:case 0x14:case 0x1c:case 0x24:case 0x2c:case 0x34:case 0x3c:case 0xa8:o=(Operand){1,0,0};g=op==0xa8?4:op>>3&7;v=alu8(g,get8(o),byte());if(g!=7&&op!=0xa8)put8(o,v);break;
 case 0xfe:m=byte();g=m>>3&7;o=decode(m,fs);if(g>1)goto unsupported;{unsigned old=cflag;v=alu8(g?5:0,get8(o),1);put8(o,v);cflag=old;}break;
 case 0xf6:m=byte();g=m>>3&7;o=decode(m,fs);a=get8(o);if(g==0){b=byte();(void)alu8(4,a,b);}else if(g==2)put8(o,~a);else if(g==3)put8(o,alu8(5,0,a));else goto unsupported;break;
 case 0x88:case 0x8a:m=byte();g=m>>3&7;o=decode(m,fs);if(op==0x88)put8(o,get8((Operand){1,g,0}));else put8((Operand){1,g,0},get8(o));break;
 case 0xc6:m=byte();if((m>>3&7)!=0)goto unsupported;o=decode(m,fs);v=byte();put8(o,v);break;
 case 0x0f:m=byte();if(m>=0x80&&m<=0x8f){v=imm();if(condition(m&15))ip=ga(ip,v);}else if(m==0xb6||m==0xbe||m==0xb7||m==0xbf){unsigned mm=byte();o=decode(mm,fs);v=(m&1)?get16(o):get8(o);r[mm>>3&7]=m==0xbe?(uint32_t)(int32_t)(int8_t)v:m==0xbf?(uint32_t)(int32_t)(int16_t)v:v;}else if(m>=0x90&&m<=0x9f){o=decode(byte(),fs);put8(o,condition(m&15));}else if(m==0xaf){unsigned mm=byte();o=decode(mm,fs);g=mm>>3&7;int64_t product=(int64_t)(int32_t)r[g]*(int32_t)get(o);r[g]=(uint32_t)product;cflag=oflag=product!=(int64_t)(int32_t)r[g];}else if(m==0xa3||m==0xab||m==0xb3||m==0xbb||m==0xba){unsigned mm=byte(),kind=mm>>3&7;o=decode(mm,fs);int32_t index;if(m==0xba){if(kind<4)goto unsupported;index=(int32_t)byte();}else{index=(int32_t)r[kind];kind=m==0xa3?4:m==0xab?5:m==0xb3?6:7;if(!o.reg){int32_t word=index>=0?index/32:(int32_t)(((int64_t)index-31)/32);o.addr=ga(o.addr,(uint32_t)word*4);}}unsigned bit=(uint32_t)index&31;uint32_t mask=UINT32_C(1)<<bit;v=get(o);cflag=(v>>bit)&1;if(kind==5)put(o,v|mask);else if(kind==6)put(o,v&~mask);else if(kind==7)put(o,gx(v,mask));}else if(m==0xbc||m==0xbd){unsigned mm=byte();o=decode(mm,fs);v=get(o);zflag=!v;if(v){unsigned bit=0;if(m==0xbc){while(!(v&(UINT32_C(1)<<bit)))bit++;}else{bit=31;while(!(v&(UINT32_C(1)<<bit)))bit--;}r[mm>>3&7]=bit;}}else if(m==0xa2){uint32_t leaf=r[0];if(leaf==0){r[0]=1;r[3]=0x756e6547;r[2]=0x49656e69;r[1]=0x6c65746e;}else if(leaf==1){r[0]=0x00000600;r[3]=0;r[1]=0;r[2]=1;}else{r[0]=r[1]=r[2]=r[3]=0;}}else if(m>=0xc8&&m<=0xcf){g=m&7;v=r[g];r[g]=(v>>24)|((v>>8)&0xff00)|((v<<8)&0xff0000)|(v<<24);}else if(m>=0x40&&m<=0x4f){unsigned mm=byte();o=decode(mm,fs);v=get(o);if(condition(m&15))r[mm>>3&7]=v;}else{report("Unsupported 0f extension %02x\n",m);goto unsupported;}break;
 case 0x98:r[0]=(uint32_t)(int32_t)(int16_t)r[0];break;
 case 0x99:if(fs)goto unsupported;r[2]=(r[0]&0x80000000u)?UINT32_MAX:0;break;
 case 0xf7:m=byte();g=m>>3&7;o=decode(m,fs);a=get(o);if(fault)break;
 if(g==0){b=imm();(void)alu(4,a,b);}
 else if(g==2)put(o,~a);
 else if(g==3)put(o,alu(5,0,a));
 else if(g==4){uint64_t product=(uint64_t)r[0]*a;r[0]=(uint32_t)product;r[2]=(uint32_t)(product>>32);cflag=oflag=(r[2]!=0);}
 else if(g==5){int64_t product=(int64_t)(int32_t)r[0]*(int32_t)a;r[0]=(uint32_t)product;r[2]=(uint32_t)((uint64_t)product>>32);cflag=oflag=(product!=(int64_t)(int32_t)r[0]);}
 else if(g==6||g==7){uint64_t bits=((uint64_t)r[2]<<32)|r[0];if(!a){report("Guest divide by zero at %08x\n",start);return 0;}if(g==6){uint64_t quot=bits/a;if(quot>UINT32_MAX){report("Guest divide overflow at %08x\n",start);return 0;}r[0]=(uint32_t)quot;r[2]=(uint32_t)(bits%a);}else{int64_t dividend=(int64_t)bits,divisor=(int32_t)a;if(dividend==INT64_MIN&&divisor==-1){report("Guest signed divide overflow at %08x\n",start);return 0;}int64_t quot=dividend/divisor;if(quot<INT32_MIN||quot>INT32_MAX){report("Guest signed divide overflow at %08x\n",start);return 0;}r[0]=(uint32_t)quot;r[2]=(uint32_t)(dividend%divisor);}}
 else goto unsupported;
 break;
 case 0xc0:case 0xd0:case 0xd2:m=byte();g=m>>3&7;o=decode(m,fs);b=op==0xc0?byte():op==0xd0?1:r[1];v=shift_group(g,get8(o),b,8);put8(o,v);break;
 case 0xc1:case 0xd1:case 0xd3:m=byte();g=m>>3&7;o=decode(m,fs);b=op==0xc1?byte():op==0xd1?1:r[1];v=shift_group(g,get(o),b,32);put(o,v);break;
 case 0x69:case 0x6b:m=byte();g=m>>3&7;o=decode(m,fs);b=op==0x69?imm():(uint32_t)(int32_t)(int8_t)byte();{int64_t product=(int64_t)(int32_t)get(o)*(int32_t)b;r[g]=(uint32_t)product;cflag=oflag=product!=(int64_t)(int32_t)r[g];}break;
 case 0xff:m=byte();g=m>>3&7;o=decode(m,fs);if(g==2||g==4){v=get(o);int ap=api_call(v,g==2);if(ap==0)return 0;if(ap==1)break;if(v>=base&&v-base<size){if(g==2)push(ip);ip=v;break;}report("Indirect transfer not implemented at %08x target=%08x slot=%08x\n",start,v,o.addr);return 0;}if(g==6){v=get(o);push(v);break;}if(g<=1){unsigned old=cflag;v=alu(g?5:0,get(o),1);put(o,v);cflag=old;break;}goto unsupported;
 default:goto unsupported;}
 completed:
 if(fault){report("Guest memory stop at %08x op=%02x\n",start,op);return 0;}trace_ring[trace_count%TRACE_LEN]=(TraceEntry){start,ip,op,(cflag?1u:0u)|(zflag?2u:0u)|(sflag?4u:0u)|(oflag?8u:0u)};trace_count++;steps++;if(steps<=128)report("%03u %08x %s%02x -> %08x\n",steps,start,os16?"66 ":fs?"64 ":"",op,ip);return 1;
 unsupported:report("Unsupported x86 at %08x opcode=%02x\n",start,op);return 0;}
static int load(const char*path){uint8_t dos[64],coff[24],opt[512],sec[40];FILE*f=fopen(path,"rb");if(!f){report("EXE open failed\n");return 0;}int ok=0;if(fread(dos,1,64,f)!=64||le16(dos)!=0x5a4d)goto done;uint32_t off=le32(dos+60);if(off>0x100000||fseek(f,off,SEEK_SET)||fread(coff,1,24,f)!=24||le32(coff)!=0x4550||le16(coff+4)!=0x14c)goto done;unsigned n=le16(coff+6),os=le16(coff+20);if(!n||n>96||os<96||os>sizeof opt||fread(opt,1,os,f)!=os||le16(opt)!=0x10b)goto done;base=le32(opt+28);size=le32(opt+56);uint32_t entry=le32(opt+16),headers=le32(opt+60);if(!size||size>64u*1024*1024||entry>=size||headers>size||(uint64_t)base+size>BASESTACK)goto done;image=calloc(1,size);stack=calloc(1,STACKSIZE);heap=calloc(1,HEAPSIZE);if(!image||!stack||!heap)goto done;if(fseek(f,0,SEEK_SET)||fread(image,1,headers,f)!=headers)goto done;for(unsigned i=0;i<n;i++){if(fseek(f,off+24+os+40*i,SEEK_SET)||fread(sec,1,40,f)!=40)goto done;uint32_t va=le32(sec+12),len=le32(sec+16),raw=le32(sec+20);if((uint64_t)va+len>size)goto done;if(len&&(fseek(f,raw,SEEK_SET)||fread(image+va,1,len,f)!=len))goto done;}ip=base+entry;r[4]=BASESTACK+STACKSIZE-16;memset(teb,0,sizeof teb);write32(TEBBASE,0xffffffffu);write32(TEBBASE+4,BASESTACK+STACKSIZE);write32(TEBBASE+8,BASESTACK);write32(TEBBASE+0x18,TEBBASE);report("PE32 base=%08x image=%u sections=%u entry=%08x\n",base,size,n,ip);if(os>=112){imports_rva=le32(opt+104);imports_size=le32(opt+108);report("Imports RVA=%08x\n",imports_rva);if(!bind_imports())goto done;}ok=1;done:fclose(f);if(!ok)report("PE loader rejected image\n");return ok;}
static int test(void){double z;cflag=0;if(shift_group(0,0x81,1,8)!=3||!cflag||!oflag)return 0;cflag=1;if(shift_group(3,0,1,32)!=0x80000000u||cflag!=0||!oflag)return 0;if(shift_group(7,0x8000,3,16)!=0xf000)return 0;if(shift_group(4,1,32,32)!=1)return 0;if(!fp_push(3.0)||!fp_push(9.0)||!fp_arith(6,fp_get(0),fp_get(1),&z)||z!=3.0)return 0;fp_compare(1,2);if(!(fp_sw()&0x100)||!fp_pop()||!fp_pop()||fp_mask)return 0;fp_top=fp_status=0;uint32_t s=0x12345678;for(unsigned i=0;i<1024;i++){s=s*1664525u+1013904223u;uint32_t a=s;s=s*1664525u+1013904223u;uint32_t b=s;if(ga(a,b)!=a+b||gx(a,b)!=(a^b)||gs(a,b)!=a-b)return 0;}if(alu(7,0,1)!=0xffffffffu||!cflag||!sflag||!condition(2)||condition(4))return 0;if(alu(7,0x80000000u,1)!=0x7fffffffu||!oflag||!condition(12))return 0;if(alu(7,42,42)!=0||!condition(4)||!pflag)return 0;for(unsigned a=0;a<256;a++)for(unsigned b=0;b<256;b++){unsigned v=alu8(7,a,b);if(v!=((a-b)&255)||cflag!=(a<b)||zflag!=(a==b)||sflag!=(v>>7))return 0;}if(alu16(0,65535,1)!=0||!zflag||!cflag)return 0;if(alu16(7,0x8000,1)!=0x7fff||!oflag)return 0;cflag=1;if(alu(2,UINT32_MAX,0)!=0||!cflag||!zflag)return 0;cflag=1;if(alu(3,0,UINT32_MAX)!=0||!cflag||!zflag)return 0;cflag=1;if(alu8(2,127,0)!=128||!oflag)return 0;cflag=1;if(alu16(3,0,0)!=65535||!cflag)return 0;return 1;}
static int run(const char*path){report("Skrillex R35 (no Wine)\n");if(!test()){report("ALU FAIL\n");return 1;}report("ALU PASS: 3072 graph arithmetic, 65536 byte comparisons, flag checks\n");zflag=sflag=cflag=oflag=pflag=aflag=dflag=0;if(path&&load(path)){for(unsigned i=0;i<100000;i++)if(!step())break;if(steps==100000)report("Instruction budget reached\n");report("Last executed instructions:\n");unsigned begin=trace_count>TRACE_LEN?trace_count-TRACE_LEN:0;
 for(unsigned i=begin;i<trace_count;i++){TraceEntry*t=&trace_ring[i%TRACE_LEN];report("%u %08x %02x -> %08x flags=%x\n",i+1,t->from,t->op,t->to,t->flags);}
 report("Registers EAX=%08x ECX=%08x EDX=%08x EBX=%08x ESP=%08x EBP=%08x ESI=%08x EDI=%08x EIP=%08x\n",r[0],r[1],r[2],r[3],r[4],r[5],r[6],r[7],ip);
 report("Executed guest instructions: %u\n",steps);report("Win32 calls completed: %u; reference frames: %u\n",api_calls,d3d_frames);}else if(path){free(image);free(stack);free(heap);return 2;}d3d_cleanup();close_guest_files();free(image);free(stack);free(heap);return 0;}
#ifdef __SWITCH__
int main(void){consoleInit(NULL);PadState pad;padConfigureInput(1,HidNpadStyleSet_NpadStandard);padInitializeDefault(&pad);logfile=fopen("sdmc:/switch/Skrillex-R35.log","w");run("sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe");if(logfile){fclose(logfile);logfile=NULL;}report("B/+ exits\n");while(appletMainLoop()){padUpdate(&pad);if(padGetButtonsDown(&pad)&(HidNpadButton_B|HidNpadButton_Plus))break;consoleUpdate(NULL);}consoleExit(NULL);return 0;}
#else
int main(int argc,char**argv){return run(argc>1?argv[1]:NULL);}
#endif
