/* ngspice 42 seeds the generator of its trnoise sources from getpid() when it starts.
 * Preloaded, this file makes getpid() return the value of the variable FAKEPID.
 * The binary of the simulator is not modified. With the same FAKEPID a run draws the same noise;
 * with another it draws another. Without FAKEPID nothing changes. */
#define _GNU_SOURCE
#include <stdlib.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <sys/types.h>

pid_t getpid(void)
{
    const char *s = getenv("FAKEPID");
    if (s)
        return (pid_t) atoi(s);
    return (pid_t) syscall(SYS_getpid);
}
