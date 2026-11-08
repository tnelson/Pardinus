#ifndef PARDINUS_ZLIB_STUB_H
#define PARDINUS_ZLIB_STUB_H
typedef void *gzFile;
#ifdef __cplusplus
extern "C" {
#endif
int gzread(gzFile file, void *buf, unsigned len);
#ifdef __cplusplus
}
#endif
#endif
