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
#define TEBBASE 0x7ffde000u
static uint8_t teb[4096];
static unsigned zflag,sflag,cflag,oflag,pflag,aflag;
static uint32_t imports_rva,imports_size;
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
static void commonflags(uint32_t v){zflag=!v;sflag=v>>31;pflag=1;for(unsigned i=0;i<8;i++)pflag^=(v>>i)&1;}
static uint32_t alu(unsigned g,uint32_t a,uint32_t b){uint32_t v=0;if(g==0){v=ga(a,b);cflag=v<a;oflag=(~(a^b)&(a^v))>>31;aflag=(a^b^v)>>4&1;}else if(g==5||g==7){v=gs(a,b);cflag=a<b;oflag=((a^b)&(a^v))>>31;aflag=(a^b^v)>>4&1;}else{v=g==1?(a|b):g==4?(a&b):gx(a,b);cflag=oflag=aflag=0;}commonflags(v);return v;}
static unsigned condition(unsigned c){switch(c&15){case 0:return oflag;case 1:return !oflag;case 2:return cflag;case 3:return !cflag;case 4:return zflag;case 5:return !zflag;case 6:return cflag||zflag;case 7:return !cflag&&!zflag;case 8:return sflag;case 9:return !sflag;case 10:return pflag;case 11:return !pflag;case 12:return sflag!=oflag;case 13:return sflag==oflag;case 14:return zflag||sflag!=oflag;default:return !zflag&&sflag==oflag;}}
static uint8_t* ptr(uint32_t a,unsigned n){if(a>=base&&(uint64_t)a-base+n<=size)return image+(a-base);if(a>=BASESTACK&&(uint64_t)a-BASESTACK+n<=STACKSIZE)return stack+(a-BASESTACK);if(a>=TEBBASE&&(uint64_t)a-TEBBASE+n<=sizeof teb)return teb+(a-TEBBASE);fault=1;return NULL;}
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
static const char* namestr(uint32_t rva){if(rva>=size||!memchr(image+rva,0,size-rva))return NULL;return (const char*)(image+rva);}
static int import_name(uint32_t slot){if(slot<base||!imports_rva||imports_rva>=size)return 0;uint32_t target=slot-base;for(uint32_t i=0;i+20<=imports_size&&i+20<=size-imports_rva;i+=20){uint8_t*d=image+imports_rva+i;uint32_t orig=le32(d),nr=le32(d+12),iat=le32(d+16);if(!nr||!iat)break;if(target<iat||(target-iat)%4)continue;uint32_t k=(target-iat)/4,lookup=orig?orig:iat;if(lookup>=size||k>=(size-lookup)/4)continue;int valid=1;for(uint32_t j=0;j<=k;j++)if(!le32(image+lookup+j*4)){valid=0;break;}if(!valid)continue;uint32_t ent=le32(image+lookup+k*4);const char*dll=namestr(nr);if(!dll)continue;if(ent&0x80000000u){report("Unresolved import %s ordinal %u\n",dll,ent&65535);return 1;}const char*name=ent<=size-2?namestr(ent+2):NULL;if(name){report("Unresolved import %s!%s\n",dll,name);return 1;}}return 0;}
static int step(void){uint32_t start=ip,v,a,b;unsigned op=byte(),m,g,fs=0;Operand o;if(fault)return 0;if(op==0x64){fs=1;op=byte();if(fault)return 0;}
 if(op>=0x50&&op<=0x57&&!fs){v=r[op-0x50];push(v);}
 else if(op>=0x58&&op<=0x5f&&!fs){v=pop();r[op-0x58]=v;}
 else if(op>=0xb8&&op<=0xbf&&!fs)r[op-0xb8]=imm();
 else if(op>=0x70&&op<=0x7f){v=(uint32_t)(int32_t)(int8_t)byte();if(condition(op&15))ip=ga(ip,v);}
 else if(op>=0x40&&op<=0x4f){unsigned old=cflag;g=op&7;r[g]=alu(op<0x48?0:5,r[g],1);cflag=old;}
 else if(op>=0x91&&op<=0x97&&!fs){g=op&7;v=r[0];r[0]=r[g];r[g]=v;}
 else if(op>=0xb0&&op<=0xb7){o=(Operand){1,op&7,0};put8(o,byte());}
 else switch(op){
 case 0x90:if(fs)goto unsupported;break;
 case 0x68:v=imm();push(v);break;case 0x6a:v=(uint32_t)(int32_t)(int8_t)byte();push(v);break;
 case 0xe8:v=imm();push(ip);ip=ga(ip,v);break;case 0xe9:v=imm();ip=ga(ip,v);break;case 0xeb:v=(uint32_t)(int32_t)(int8_t)byte();ip=ga(ip,v);break;
 case 0xc2:v=imm16();ip=pop();r[4]=ga(r[4],v);break;case 0xc3:ip=pop();break;case 0xc9:r[4]=r[5];r[5]=pop();break;
 case 0xa1:v=imm();r[0]=read32(fs?ga(v,TEBBASE):v);break;case 0xa3:v=imm();write32(fs?ga(v,TEBBASE):v,r[0]);break;
 case 0x89:case 0x8b:case 0x8d:case 0x31:case 0x33:case 0x2b:case 0x29:case 0x85:case 0x01:case 0x03:case 0x39:case 0x3b:case 0x21:case 0x23:case 0x09:case 0x0b:
 m=byte();g=m>>3&7;o=decode(m,op==0x8d?0:fs);if(fault)break;
 if(op==0x89)put(o,r[g]);else if(op==0x8b)r[g]=get(o);else if(op==0x8d){if(o.reg)goto unsupported;r[g]=o.addr;}
 else if(op==0x85){(void)alu(4,get(o),r[g]);}
 else{unsigned group=(op>>3)&7;unsigned dest=op&2;if(dest){v=alu(group,r[g],get(o));if(group!=7)r[g]=v;}else{v=alu(group,get(o),r[g]);if(group!=7)put(o,v);}}
 break;
 case 0x87:m=byte();g=m>>3&7;o=decode(m,fs);v=get(o);put(o,r[g]);r[g]=v;break;
 case 0xc7:m=byte();if((m>>3&7)!=0)goto unsupported;o=decode(m,fs);v=imm();put(o,v);break;
 case 0x81:case 0x83:m=byte();g=m>>3&7;o=decode(m,fs);b=op==0x81?imm():(uint32_t)(int32_t)(int8_t)byte();a=get(o);if(g==2||g==3)goto unsupported;v=alu(g,a,b);if(g!=7)put(o,v);break;
 case 0x05:case 0x0d:case 0x25:case 0x2d:case 0x35:case 0x3d:g=op>>3&7;v=imm();v=alu(g,r[0],v);if(g!=7)r[0]=v;break;
 case 0xa9:v=imm();(void)alu(4,r[0],v);break;
 case 0x88:case 0x8a:m=byte();g=m>>3&7;o=decode(m,fs);if(op==0x88)put8(o,get8((Operand){1,g,0}));else put8((Operand){1,g,0},get8(o));break;
 case 0xc6:m=byte();if((m>>3&7)!=0)goto unsupported;o=decode(m,fs);v=byte();put8(o,v);break;
 case 0x0f:m=byte();if(m>=0x80&&m<=0x8f){v=imm();if(condition(m&15))ip=ga(ip,v);}else if(m==0xb6||m==0xbe){unsigned mm=byte();o=decode(mm,fs);v=get8(o);r[mm>>3&7]=m==0xbe?(uint32_t)(int32_t)(int8_t)v:v;}else{report("Unsupported 0f extension %02x\n",m);goto unsupported;}break;
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
 case 0xc1:case 0xd1:case 0xd3:m=byte();g=m>>3&7;o=decode(m,fs);b=(op==0xc1?byte():op==0xd1?1:r[1])&31;a=get(o);if(g!=4&&g!=5&&g!=7)goto unsupported;if(!b)break;if(g==4){v=a<<b;cflag=a>>(32-b)&1;if(b==1)oflag=(v>>31)^cflag;}else{cflag=a>>(b-1)&1;v=g==5?a>>b:(uint32_t)((int32_t)a>>b);if(b==1)oflag=g==5?a>>31:0;}commonflags(v);put(o,v);break;
 case 0x69:case 0x6b:m=byte();g=m>>3&7;o=decode(m,fs);b=op==0x69?imm():(uint32_t)(int32_t)(int8_t)byte();{int64_t product=(int64_t)(int32_t)get(o)*(int32_t)b;r[g]=(uint32_t)product;cflag=oflag=product!=(int64_t)(int32_t)r[g];}break;
 case 0xff:m=byte();g=m>>3&7;o=decode(m,fs);if(g==2||g==4){v=get(o);if(!o.reg&&import_name(o.addr))return 0;if(v>=base&&v-base<size){if(g==2)push(ip);ip=v;break;}report("Indirect transfer not implemented at %08x target=%08x slot=%08x\n",start,v,o.addr);return 0;}if(g==6){v=get(o);push(v);break;}goto unsupported;
 default:goto unsupported;}
 if(fault){report("Guest memory stop at %08x op=%02x\n",start,op);return 0;}steps++;if(steps<=128)report("%03u %08x %s%02x -> %08x\n",steps,start,fs?"64 ":"",op,ip);return 1;
 unsupported:report("Unsupported x86 at %08x opcode=%02x\n",start,op);return 0;}
static int load(const char*path){uint8_t dos[64],coff[24],opt[512],sec[40];FILE*f=fopen(path,"rb");if(!f){report("EXE open failed\n");return 0;}int ok=0;if(fread(dos,1,64,f)!=64||le16(dos)!=0x5a4d)goto done;uint32_t off=le32(dos+60);if(off>0x100000||fseek(f,off,SEEK_SET)||fread(coff,1,24,f)!=24||le32(coff)!=0x4550||le16(coff+4)!=0x14c)goto done;unsigned n=le16(coff+6),os=le16(coff+20);if(!n||n>96||os<96||os>sizeof opt||fread(opt,1,os,f)!=os||le16(opt)!=0x10b)goto done;base=le32(opt+28);size=le32(opt+56);uint32_t entry=le32(opt+16),headers=le32(opt+60);if(!size||size>64u*1024*1024||entry>=size||headers>size||(uint64_t)base+size>BASESTACK)goto done;image=calloc(1,size);stack=calloc(1,STACKSIZE);if(!image||!stack)goto done;if(fseek(f,0,SEEK_SET)||fread(image,1,headers,f)!=headers)goto done;for(unsigned i=0;i<n;i++){if(fseek(f,off+24+os+40*i,SEEK_SET)||fread(sec,1,40,f)!=40)goto done;uint32_t va=le32(sec+12),len=le32(sec+16),raw=le32(sec+20);if((uint64_t)va+len>size)goto done;if(len&&(fseek(f,raw,SEEK_SET)||fread(image+va,1,len,f)!=len))goto done;}ip=base+entry;r[4]=BASESTACK+STACKSIZE-16;memset(teb,0,sizeof teb);write32(TEBBASE,0xffffffffu);write32(TEBBASE+4,BASESTACK+STACKSIZE);write32(TEBBASE+8,BASESTACK);write32(TEBBASE+0x18,TEBBASE);report("PE32 base=%08x image=%u sections=%u entry=%08x\n",base,size,n,ip);if(os>=112){imports_rva=le32(opt+104);imports_size=le32(opt+108);report("Imports RVA=%08x (unresolved)\n",imports_rva);}ok=1;done:fclose(f);if(!ok)report("PE loader rejected image\n");return ok;}
static int test(void){uint32_t s=0x12345678;for(unsigned i=0;i<1024;i++){s=s*1664525u+1013904223u;uint32_t a=s;s=s*1664525u+1013904223u;uint32_t b=s;if(ga(a,b)!=a+b||gx(a,b)!=(a^b)||gs(a,b)!=a-b)return 0;}if(alu(7,0,1)!=0xffffffffu||!cflag||!sflag||!condition(2)||condition(4))return 0;if(alu(7,0x80000000u,1)!=0x7fffffffu||!oflag||!condition(12))return 0;if(alu(7,42,42)!=0||!condition(4)||!pflag)return 0;return 1;}
static int run(const char*path){report("Skrillex R06 (no Wine)\n");if(!test()){report("ALU FAIL\n");return 1;}report("ALU PASS: 3072 checks\n");if(path&&load(path)){for(unsigned i=0;i<4096;i++)if(!step())break;report("Executed guest instructions: %u\n",steps);report("Win32 imports and graphics not implemented\n");}else if(path){free(image);free(stack);return 2;}free(image);free(stack);return 0;}
#ifdef __SWITCH__
int main(void){consoleInit(NULL);PadState pad;padConfigureInput(1,HidNpadStyleSet_NpadStandard);padInitializeDefault(&pad);logfile=fopen("sdmc:/switch/Skrillex-R06.log","w");run("sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe");if(logfile){fclose(logfile);logfile=NULL;}report("B/+ exits\n");while(appletMainLoop()){padUpdate(&pad);if(padGetButtonsDown(&pad)&(HidNpadButton_B|HidNpadButton_Plus))break;consoleUpdate(NULL);}consoleExit(NULL);return 0;}
#else
int main(int argc,char**argv){return run(argc>1?argv[1]:NULL);}
#endif
