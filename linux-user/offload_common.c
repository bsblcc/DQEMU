#include "offload_common.h"


__thread char *p;

pthread_mutex_t global_counter_mutex = PTHREAD_MUTEX_INITIALIZER;
int global_counter;
int client_port_of(int idx)
{
	return PORT_BASE + idx * 2;
}


int server_port_of(int idx)
{
	return PORT_BASE + idx * 2 + 1;
}

__thread int offload_mode;
int offload_server_idx;
__thread int offload_client_idx;



#define PRTCTRL_NONE "\e[0m"
#define PRTCTRL_RED "\e[0;31m"
#define PRTCTRL_GREEN "\e[0;32m"
void offload_log(FILE *f, const char *c, ...)
{
	char tmp[1000] = "";

	if (offload_mode == 1)
	{
		sprintf(tmp, PRTCTRL_RED "[server #%d]\t", offload_server_idx);
	}
	else if (offload_mode == 2)
	{
		sprintf(tmp, PRTCTRL_GREEN "[client #%d]\t", offload_client_idx);
	}
	else if (offload_mode == 3)
	{
		sprintf(tmp, "[exec #%d]\t", offload_server_idx);
	}
	strcat(tmp, c);
	strcat(tmp, PRTCTRL_NONE);
    va_list args;
    va_start(args, tmp);
    vfprintf(f, tmp, args);
    va_end(args);
}
