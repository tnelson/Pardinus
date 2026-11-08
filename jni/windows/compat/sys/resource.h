#ifndef PARDINUS_SYS_RESOURCE_H
#define PARDINUS_SYS_RESOURCE_H

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#include <sys/time.h>

#define RUSAGE_SELF 0

struct rusage {
  struct timeval ru_utime;
  struct timeval ru_stime;
};

static inline void pardinus_filetime_to_timeval(FILETIME ft, struct timeval *tv) {
  unsigned long long t = ((unsigned long long)ft.dwHighDateTime << 32) | ft.dwLowDateTime;
  tv->tv_sec = (long)(t / 10000000ULL);
  tv->tv_usec = (long)((t % 10000000ULL) / 10ULL);
}

static inline int getrusage(int who, struct rusage *usage) {
  FILETIME created, exited, kernel, user;
  if (who != RUSAGE_SELF) return -1;
  if (!GetProcessTimes(GetCurrentProcess(), &created, &exited, &kernel, &user)) return -1;
  pardinus_filetime_to_timeval(user, &usage->ru_utime);
  pardinus_filetime_to_timeval(kernel, &usage->ru_stime);
  return 0;
}

#endif
