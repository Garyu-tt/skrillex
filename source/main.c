#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#ifdef __SWITCH__
#include <switch.h>
#endif
#define BASESTACK 0x70000000u
#define STACKSIZE (1024u*1024u)
static uint8_t *image,*stack;
static uint32_t base,size,ip,r[8];
static int fault;
static FILE *logfile;
static unsigned steps;
static void report(const char *fmt,...){va_list a;va_start(a,fmt);vprintf(fmt,a);va_end(a);if(logfile){va_start(a,fmt);vfprintf(logfile,fmt,a);va_end(a);fflush(logfile);}}
static uint32_t le32(const uint8_t*p){return (uint32_t)p[0]|(uint32_t)p[1]<<8|(uint32_t)p[2]<<16|(uint32_t)p[3]<<24;}
static unsigned le16(const uint8_t*p){return p[0]|p[1]<<8;}
static unsigned gate(unsigned a,unsigned b,unsigned t){return a+b>=t;}
static unsigned xorbit(unsigned a,unsigned b){return gate(gate(a,b,1),!gate(a,b,2),2);}
static uint32_t gx(uint32_t a,uint32_t b){uint32_t z=0;for(unsigned i=0;i<32;i++)z|=(uint32_t)xorbit(a>>i&1,b>>i&1)<<i;return z;}
static uint32_t ga(uint32_t a,uint32_t b){uint32_t z=0;unsigned c=0;for(unsigned i=0;i<32;i++){unsigned x=a>>i&1,y=b>>i&1,p=xorbit(x,y);z|=(uint32_t)xorbit(p,c)<<i;c=gate(gate(x,y,2),gate(p,c,2),1);}return z;}
static uint32_t gs(uint32_t a,uint32_t b){return ga(a,ga(~b,1));}
static uint8_t* ptr(uint32_t a,unsigned n){if(a>=base&&(uint64_t)a-base+n<=size)return image+(a-base);if(a>=BASESTACK&&(uint64_t)a-BASESTACK+n<=STACKSIZE)return stack+(a-BASESTACK);fault=1;return NULL;}
static uint32_t read32(uint32_t a){uint8_t*p=ptr(a,4);return p?le32(p):0;}
static void write32(uint32_t a,uint32_t v){uint8_t*p=ptr(a,4);if(p)for(unsigned i=0;i<4;i++)p[i]=v>>(i*8);}
static unsigned byte(void){uint8_t*p=ptr(ip,1);if(!p)return 0;ip++;return *p;}
static uint32_t imm(void){uint32_t v=read32(ip);if(!fault)ip+=4;return v;}
static void push(uint32_t v){r[4]=gs(r[4],4);write32(r[4],v);}
static uint32_t pop(void){uint32_t v=read32(r[4]);r[4]=ga(r[4],4);return v;}
static int step(void){uint32_t start=ip,v;unsigned op=byte(),m; if(fault)return 0;
 if(op>=0x50&&op<=0x57){v=r[op-0x50];push(v);}else if(op>=0x58&&op<=0x5f){v=pop();r[op-0x58]=v;}else if(op>=0xb8&&op<=0xbf)r[op-0xb8]=imm();else switch(op){
 case 0x90:break;case 0x68:v=imm();push(v);break;case 0x6a:v=(uint32_t)(int32_t)(int8_t)byte();push(v);break;case 0xe8:v=imm();push(ip);ip=ga(ip,v);break;case 0xe9:v=imm();ip=ga(ip,v);break;case 0xeb:v=(uint32_t)(int32_t)(int8_t)byte();ip=ga(ip,v);break;case 0xc3:ip=pop();break;case 0xc9:r[4]=r[5];r[5]=pop();break;
 case 0x89:case 0x8b:case 0x31:case 0x33:m=byte();if((m>>6)!=3)goto unsupported;if(op==0x89)r[m&7]=r[m>>3&7];else if(op==0x8b)r[m>>3&7]=r[m&7];else if(op==0x31)r[m&7]=gx(r[m&7],r[m>>3&7]);else r[m>>3&7]=gx(r[m>>3&7],r[m&7]);break;
 default:goto unsupported;}
 if(fault){report("Guest memory stop at %08x op=%02x\n",start,op);return 0;}steps++;if(steps<=64)report("%03u %08x %02x -> %08x\n",steps,start,op,ip);return 1;
 unsupported:report("Unsupported x86 at %08x opcode=%02x\n",start,op);return 0;}
static int load(const char*path){uint8_t dos[64],coff[24],opt[512],sec[40];FILE*f=fopen(path,"rb");if(!f){report("EXE open failed\n");return 0;}int ok=0;if(fread(dos,1,64,f)!=64||le16(dos)!=0x5a4d)goto done;uint32_t off=le32(dos+60);if(off>0x100000||fseek(f,off,SEEK_SET)||fread(coff,1,24,f)!=24||le32(coff)!=0x4550||le16(coff+4)!=0x14c)goto done;unsigned n=le16(coff+6),os=le16(coff+20);if(!n||n>96||os<96||os>sizeof opt||fread(opt,1,os,f)!=os||le16(opt)!=0x10b)goto done;base=le32(opt+28);size=le32(opt+56);uint32_t entry=le32(opt+16),headers=le32(opt+60);if(!size||size>64u*1024*1024||entry>=size||headers>size||(uint64_t)base+size>BASESTACK)goto done;image=calloc(1,size);stack=calloc(1,STACKSIZE);if(!image||!stack)goto done;if(fseek(f,0,SEEK_SET)||fread(image,1,headers,f)!=headers)goto done;for(unsigned i=0;i<n;i++){if(fseek(f,off+24+os+40*i,SEEK_SET)||fread(sec,1,40,f)!=40)goto done;uint32_t va=le32(sec+12),len=le32(sec+16),raw=le32(sec+20);if((uint64_t)va+len>size)goto done;if(len&&(fseek(f,raw,SEEK_SET)||fread(image+va,1,len,f)!=len))goto done;}ip=base+entry;r[4]=BASESTACK+STACKSIZE-16;report("PE32 base=%08x image=%u sections=%u entry=%08x\n",base,size,n,ip);if(os>=112)report("Imports RVA=%08x (unresolved)\n",le32(opt+104));ok=1;done:fclose(f);if(!ok)report("PE loader rejected image\n");return ok;}
static int test(void){uint32_t s=0x12345678;for(unsigned i=0;i<1024;i++){s=s*1664525u+1013904223u;uint32_t a=s;s=s*1664525u+1013904223u;uint32_t b=s;if(ga(a,b)!=a+b||gx(a,b)!=(a^b)||gs(a,b)!=a-b)return 0;}return 1;}
static int run(const char*path){report("NeroExec R03 (no Wine)\n");if(!test()){report("ALU FAIL\n");return 1;}report("ALU PASS: 3072 checks\n");if(path&&load(path)){for(unsigned i=0;i<4096;i++)if(!step())break;report("Executed guest instructions: %u\n",steps);report("Win32 imports and graphics not implemented\n");}else if(path){free(image);free(stack);return 2;}free(image);free(stack);return 0;}
#ifdef __SWITCH__
int main(void){consoleInit(NULL);PadState pad;padConfigureInput(1,HidNpadStyleSet_NpadStandard);padInitializeDefault(&pad);logfile=fopen("sdmc:/switch/NeroExec-R03.log","w");run("sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe");if(logfile){fclose(logfile);logfile=NULL;}report("B/+ exits\n");while(appletMainLoop()){padUpdate(&pad);if(padGetButtonsDown(&pad)&(HidNpadButton_B|HidNpadButton_Plus))break;consoleUpdate(NULL);}consoleExit(NULL);return 0;}
#else
int main(int argc,char**argv){return run(argc>1?argv[1]:NULL);}
#endif
