#define _XOPEN_SOURCE 500  /* include pread,pwrite */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <fcntl.h>
#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <dlfcn.h>
#include <elf.h>
#include <unistd.h>
#include <errno.h>       
#include <sys/mman.h>
#include "util.h"
#include "procutils.h"
#include <getopt.h>
#include <time.h>
#include <sys/time.h>



//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////

#define TIME_DIFF_FILE "/dtv/tvTimeDiff.bin"
int debug,set_time=0, utc=0,date=0,year=0,hour=0,minute=0,hour_minute=0, date2=0, time_diff=0;

//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////

// ./gdbserver --attach :9798 99 &
// text:014C8114 F9 9C C5 EB                             BL              memset
//.text:014C8134 F1 9C C5 EB                             BL              memset

//9AF844 - 009AF758 
//BD FF FF EA
// 1E FF 2F E1                             BX              LR

struct mem_patch
{
    const char *		m_name;
    unsigned long		m_offs;
    unsigned int		looplo;
    unsigned int		loophi;
    unsigned long		m_orig;
    unsigned long		m_repl;
    //const char *m_orig;
    const char *		cm_repl;
};

#define ARRAYSIZE(AR) (sizeof(AR)/sizeof(AR[0]))

//adbg_CheckSystem
//bx lr
static void __attribute__((noinline,naked)) set_font()
{
    asm volatile (
		"mov r0, pc\n"
		"b l_size\n"
		"nop\n"
		"nop\n"
		"nop\n"
		"nop\n"
		"l_size: ldr r1, [r0], #4\n"
		"ldr r10, [r0,r5, LSL #2]\n"
		"add r0, pc, #4\n"
		"str r1, [r0,#8]\n"
		"mov r0, #1\n"
		"mov r1, #3\n"
    		"ldr pc, [pc, #-4]\n"
		"nop\n\t"
	 	);
}
static void __attribute__((noinline,naked)) set_font_end() {asm ("nop");}


static void __attribute__((noinline,naked)) _ldr_r0_r4_0x60() {asm ("ldr r0, [r4, #0x60]");}
static void __attribute__((noinline,naked)) _movw_r1_0() {asm ("movw r1, #0");}
static void __attribute__((noinline,naked)) _movt_r1_0() {asm ("movt r1, #0");}
static void __attribute__((noinline,naked)) BRANCH_HOOK() {asm ("ldr pc, [pc, #-4]");}
static void __attribute__((noinline,naked)) _add_r3_r3_0x248() {asm ("add r3,r3,#0x248");}

#define ADD_R3_R3_0X248        (*(uint32_t*)_add_r3_r3_0x248)
#define LDR_R0_R4_0X60        (*(uint32_t*)_ldr_r0_r4_0x60)
#define MOVW_R1_0        (*(uint32_t*)_movw_r1_0)
#define MOVT_R1_0        (*(uint32_t*)_movt_r1_0)
#define MOVW_RD 0xff00f000
#define MOVT_RD 0xfff0f000

static void __attribute__((noinline,naked)) branch_b()
{
    asm volatile (
    		"ldr pc, [pc, #-4]\n\t"
		"nop\n\t"
		);

}
static void __attribute__((noinline,naked)) branch_bl()
{
    asm volatile (
		"add lr, pc ,#4\n\t"
    		"ldr pc, [pc, #-4]\n\t"
		"nop\n\t"
		);

}
static struct mem_patch mem_patches_exeDSP[] =
{
};

unsigned long PATCH[1000];
unsigned long small=29, medium=32, large=35, color=0;
static int patch_proc(pid_t pid)
{
	struct pt_regs2 regs;
	time_t rawtime;
	struct tm * timeinfo;
	struct TimeInfo *time;
	unsigned long *p,i,get_time_addr,g_pAppTV=0,g_AppTV=0, get_time_zone;
	unsigned long add_num,cur_addr,p_addr,p_len,branch_addr,tmp,addr;
	int fd = 0;
	char buf[1024];

	struct mem_patch *mem_patches = 0;
	int mem_patch_cnt = 0;
	sprintf(buf, "/proc/%d/exe", pid);
	buf[readlink(buf, buf, sizeof(buf))] = 0;
	symtab_t symtab = load_symtab(buf);
	if(!symtab) {
		fprintf(stderr, "Error loading symbol table for: %s [%d]\n", buf, pid);
		exit(0);
	}
    
 	// Attach 
	if (0 > ptrace(PTRACE_ATTACH, pid, 0, 0)) {
		printf("cannot attach to %d, error!\n", pid);
		exit(1);
	}
	waitpid(pid, NULL, 0);
	
	sprintf(buf, "/proc/%d/mem", pid);
	fd = open(buf, O_WRONLY);
	if (0 > fd) {
		printf("cannot open %s, error!\n", buf);
		exit(1);
	}
	ptrace(PTRACE_GETREGS, pid, 0, &regs);

	if (debug) {
		printf("pc=%x lr=%x sp=%x fp=%x\n", (uint)regs.ARM_pc, (uint)regs.ARM_lr, (uint)regs.ARM_sp, (uint)regs.ARM_fp);
		printf("r0=%x r1=%x\n", (uint)regs.ARM_r0, (uint)regs.ARM_r1);
		printf("r2=%x r3=%x\n", (uint)regs.ARM_r2, (uint)regs.ARM_r3);
	}
	
	
	g_AppTV=get_object_by_name(symtab,"g_AppTV");
	if(!g_AppTV)
	{
		g_pAppTV=get_object_by_name(symtab,"g_pAppTV");
		if(g_pAppTV)
			read_mem(pid,&g_AppTV,1,g_pAppTV);

	}
	get_time_zone=get_func_by_name(symtab,"_ZN4TCTv11GetTimeZoneEPiS0_i");
	if(!get_time_zone)
	{
		get_time_zone=get_func_by_name(symtab,"_ZN4TCTv11GetTimeZoneEPiS0_");
		if(!get_time_zone)
			get_time_zone=get_func_by_name(symtab,"_ZN9TCTvProxy11GetTimeZoneEPiS0_");
	}
	get_time_addr=get_func_by_name(symtab,"_ZN4TCTv17GetSystemInfoTimeEPmi");
	if(!get_time_addr)
		get_time_addr=get_func_by_name(symtab,"_ZN9TCTvProxy17GetSystemInfoTimeEPmi");
	if(g_AppTV && get_time_addr && get_time_zone)
	{
		struct timeval orgTime;
		if(time_diff)
		{
			unlink(TIME_DIFF_FILE);
			gettimeofday(&orgTime,0);
		}
		time=get_current_time(pid, symtab, (void*)g_AppTV, (void*)get_time_addr, (void*)get_time_zone);
		if(time)
		{
			if(date || year || hour || minute || hour_minute)
			{
				rawtime=time->currentTime+time->timeZoneOffset*60;
				timeinfo = localtime ( &rawtime );
				if(date)
					printf("%s", asctime(timeinfo));
				if(year)
					printf("%04d\n", timeinfo->tm_year+1900);
				if(hour)
					printf("%02d\n", timeinfo->tm_hour);
				if(minute)
					printf("%02d\n", timeinfo->tm_min);
				if(hour_minute)
					printf("%02d%02d\n",timeinfo->tm_hour, timeinfo->tm_min);

			}
			else if(date2)
			{
				rawtime=time->currentTime;
				timeinfo = localtime ( &rawtime );
				printf("%s", asctime(timeinfo));
			}
			else
			{
				rawtime=time->currentTime;
				printf("Current Time: %d\n",(int)rawtime);
				printf("Current TimeZone Number: %d\n",time->timeZoneNumber);
				printf("Current TimeZone Offset: %d\n",time->timeZoneOffset);
				timeinfo = localtime ( &rawtime );
				printf ( "The current date/time is: %s", asctime (timeinfo) );
				rawtime=time->currentTime+time->timeZoneOffset*60;
				timeinfo = localtime ( &rawtime );
				printf("Current Time+Offset: %d\n",(int)rawtime);
				printf ( "The current date/time+offset is: %s", asctime (timeinfo) );
			}
				
			if(set_time)
			{
				struct timespec tv_set;
				rawtime=time->currentTime+time->timeZoneOffset*60;
				tv_set.tv_sec = rawtime;
				if (clock_settime(CLOCK_REALTIME, &tv_set)<0)
					printf("Unale to set time.\n");
				else
					printf("Succesfully set current time.\n");

			}

			if(utc)
			{
				struct timespec tv_set;
				tv_set.tv_sec = time->currentTime;
				if (clock_settime(CLOCK_REALTIME, &tv_set)<0)
					printf("Unale to set time.\n");
				else
					printf("Succesfully set current time.\n");
			}
			if(time_diff)
			{
				FILE *fp;
				long tvTimeDiff;
				fp=fopen(TIME_DIFF_FILE,"w+b");
				if(fp)
				{
					tvTimeDiff=time->currentTime-orgTime.tv_sec;
					fprintf(fp, "%ld",tvTimeDiff);
					fclose(fp);
					printf("Time difference successfully saved to: %s\n",TIME_DIFF_FILE);
				}
				else
					printf("Unable to save time difference to: %s\n", TIME_DIFF_FILE);
			}
		}

	}
	else
		printf("Unable to continue. Addresses of g_AppTV and/or _ZN4TCTv17GetSystemInfoTimeEPmi not found.\n");

	// detach and continue
	ptrace(PTRACE_SETREGS, pid, 0, &regs);
	ptrace(PTRACE_DETACH, pid, 0, 0);

	if (debug)
		printf("Patching completed!\n");
}

static int on_proc_found(
        pid_t pid, void *ctx)
{
    patch_proc(pid);
    
    return 0;
}

static void usage_and_exit(const char *self)
{
	fprintf(stderr, "Get/Set Current Time From TV v0.6.1 by sectroyer\n\n", self);
	fprintf(stderr, "error usage: %s [-p PID | -n procname] -d (debug on)\n", self);
	fprintf(stderr, "\t-p, --pid\t\tpid of process to attach\n", self);
	fprintf(stderr, "\t-n, --procname\t\tname of process to attach\n", self);
	fprintf(stderr, "\t-d, --debug\t\tenable debug output\n", self);
	fprintf(stderr, "\t-D, --date\t\tdisplay only date/time+offset\n", self);
	fprintf(stderr, "\t-Y, --year\t\tdisplay only year+offset\n", self);
	fprintf(stderr, "\t-H, --hour\t\tdisplay only hour+offset\n", self);
	fprintf(stderr, "\t-M, --minute\t\tdisplay only minute+offset\n", self);
	fprintf(stderr, "\t-W, --hour-minute\t\tdisplay only hour+minute+offset\n", self);
	fprintf(stderr, "\t-U, --utc-date\t\tdisplay only date/time\n", self);
	fprintf(stderr, "\t-s, --set\t\tset time+offset to tv time\n", self);
	fprintf(stderr, "\t-u, --utc\t\tset only UTC time to tv time\n", self);
	fprintf(stderr, "\t-T, --time-diff\t\tSave time diff to /dtv/tvTimeDiff.bin\n\n", self);
	exit(0);
}
static struct option long_options[] =
     {
       {"debug", 0,  0, 'd'},
       {"set", 0,  0, 's'},
       {"utc", 0,  0, 'u'},
       {"utc-date", 0,  0, 'U'},
       {"time-diff", 0,  0, 'T'},
       {"date", 0,  0, 'D'},
       {"year", 0,  0, 'Y'},
       {"hour", 0,  0, 'H'},
       {"minute", 0,  0, 'M'},
       {"hour-minute", 0,  0, 'W'},
       {"procname",  1, 0, 'n'},
       {"pid",  1, 0, 'p'},
       {0, 0, 0, 0}
     }; 
int main(int argc, char *argv[])
{
	pid_t pid = 0;
	int  opt;
    	const char *procname = 0;
	int option_index =0;
	////
 	while ((opt = getopt_long(argc, argv, "p:n:dusDYHMWUT", long_options,&option_index)) != -1) {
		switch (opt) {
			case 'p':
				pid = strtol(optarg, NULL, 0);
			break;
			case 'n':
				procname = optarg;
			break;
			case 'd':
				debug = 1;
			break;
			case 'D':
				date = 1;
			break;
			case 'Y':
				year = 1;
			break;
			case 'H':
				hour = 1;
			break;
			case 'M':
				minute = 1;
			break;
			case 'W':
				hour_minute = 1;
			break;
			case 'U':
				date2 = 1;
			break;
			case 'T':
				time_diff = 1;
			break;
			case 's':
				set_time = 1;
			break;
			case 'u':
				utc = 1;
			break;
			default:
	            	usage_and_exit(argv[0]);
				break;
		}
	}
	if ((!!pid == !!procname) || (pid && procname)) {
	    usage_and_exit(argv[0]);
	}
	
	int rc;
	if(procname)
	    rc = proc_find_processes(procname, on_proc_found, 0);
	else
	    rc = patch_proc(pid);
	return 0;
}
