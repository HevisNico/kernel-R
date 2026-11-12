/* Runtime portability only: honor TMPDIR for anonymous temporary files.
 * No simulator equations, random-number functions or solver settings changed. */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
FILE *tmpfile(void) {
    const char *dir = getenv("TMPDIR");
    if (!dir || !*dir) { errno = EINVAL; return NULL; }
    size_t n = strlen(dir) + sizeof("/ngspice-XXXXXX");
    char *name = malloc(n);
    if (!name) return NULL;
    snprintf(name, n, "%s/ngspice-XXXXXX", dir);
    int fd = mkstemp(name);
    if (fd < 0) { free(name); return NULL; }
    unlink(name);
    free(name);
    FILE *result = fdopen(fd, "w+b");
    if (!result) close(fd);
    return result;
}
FILE *tmpfile64(void) { return tmpfile(); }
