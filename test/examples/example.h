#ifndef EXAMPLE_H
#define EXAMPLE_H

// generated with openssl genrsa for demonstration purposes;

uint8_t modulus[256] = {
  0xeb, 0x4c, 0xe9, 0xef, 0xa0, 0x61, 0x7c, 0x2b, 0x1b, 0xcf, 0x9d, 0x68, 0x61, 0xd8, 0x44, 0xda,
  0x90, 0x44, 0x6c, 0x7a, 0x7a, 0xd2, 0x83, 0x1f, 0x72, 0x45, 0x84, 0x0e, 0xe1, 0xae, 0xf0, 0x9b,
  0xe6, 0xb7, 0xaf, 0x34, 0xbc, 0x4d, 0x29, 0x92, 0xda, 0x09, 0x9b, 0x1b, 0xc6, 0x04, 0x1b, 0x38,
  0xc7, 0x87, 0xc4, 0x2a, 0x09, 0xd8, 0xbf, 0x59, 0xfb, 0xeb, 0x33, 0x77, 0xac, 0x68, 0xc4, 0x83,
  0x1e, 0x38, 0x87, 0x16, 0x21, 0x61, 0x38, 0x8c, 0x0b, 0xc8, 0xf5, 0x6b, 0x15, 0xb3, 0x96, 0x8e,
  0xd1, 0xea, 0xbd, 0x78, 0x98, 0x08, 0xca, 0x2f, 0xd0, 0xf6, 0x0b, 0x1b, 0xcf, 0xa2, 0x06, 0x5f,
  0x0a, 0x60, 0x8c, 0x69, 0x83, 0xb0, 0xd8, 0xa7, 0xbd, 0xa0, 0x3f, 0xb9, 0x35, 0x8a, 0xef, 0x8d,
  0x80, 0x76, 0xb7, 0xf7, 0x9d, 0x20, 0x7f, 0xaf, 0xf6, 0xc7, 0x23, 0xbb, 0x2a, 0x2b, 0x3e, 0x27,
  0xfd, 0x45, 0xaa, 0xe7, 0x52, 0xd2, 0xfd, 0xd5, 0xb5, 0xeb, 0x13, 0xc1, 0x32, 0xa0, 0x35, 0x8e,
  0xdc, 0x05, 0x7b, 0xa3, 0xc3, 0xf7, 0x4d, 0xa6, 0x8c, 0xc7, 0xf9, 0x71, 0xd6, 0x50, 0x6a, 0x64,
  0x9b, 0xf0, 0x49, 0xce, 0x21, 0x59, 0x90, 0xab, 0x78, 0xd4, 0x82, 0x1a, 0xf5, 0x18, 0xe7, 0x07,
  0xb8, 0x1a, 0xeb, 0xbc, 0x6a, 0x17, 0x5f, 0x05, 0x30, 0x99, 0xa8, 0xd1, 0xa7, 0xf7, 0x37, 0x49,
  0x80, 0x3f, 0xfd, 0x4a, 0x11, 0x55, 0x75, 0xb9, 0xa9, 0x33, 0x7c, 0x6e, 0x91, 0x6f, 0x90, 0xd0,
  0xc5, 0x0a, 0x63, 0xef, 0x4f, 0x41, 0x3c, 0x71, 0x9f, 0x16, 0x7f, 0x74, 0x46, 0xa5, 0x5a, 0xf8,
  0xeb, 0x86, 0xd7, 0xab, 0x15, 0x60, 0x42, 0xc7, 0xc6, 0x1f, 0x93, 0xe9, 0xc6, 0x48, 0x34, 0xf0,
  0xa8, 0x62, 0x75, 0xdb, 0x44, 0xbd, 0xbe, 0xbd, 0xef, 0x0d, 0x6b, 0x61, 0xc2, 0x24, 0xf1, 0xd1
};

uint8_t exp_d[256] = {
  0xe4, 0x08, 0x99, 0x1a, 0x62, 0xaa, 0xb7, 0x24, 0x2c, 0x02, 0xab, 0xc0, 0xd2, 0x3a, 0x3e, 0x98,
  0x36, 0x82, 0x29, 0x43, 0x15, 0xae, 0xd7, 0xe6, 0x6c, 0xdf, 0x13, 0xd9, 0x3c, 0x3c, 0x46, 0xf0,
  0x3f, 0xcb, 0x39, 0xdf, 0xf8, 0xb1, 0x2b, 0x1e, 0x27, 0x72, 0x71, 0xc0, 0x9b, 0xc9, 0xb4, 0xfb,
  0xf4, 0xdb, 0x0d, 0x6f, 0xd4, 0x35, 0x1b, 0x54, 0xc0, 0x80, 0xb3, 0x53, 0x42, 0x62, 0x12, 0x38,
  0x23, 0xdc, 0x92, 0x86, 0x0e, 0xf9, 0x62, 0x4c, 0xce, 0xcb, 0x05, 0x94, 0xae, 0xe6, 0x69, 0x7d,
  0xa5, 0xd0, 0x41, 0xa9, 0x12, 0x66, 0x4a, 0x53, 0xc6, 0xc5, 0xfc, 0x04, 0x0a, 0xd8, 0x32, 0x26,
  0x7f, 0x2f, 0x0c, 0x44, 0xe1, 0x9c, 0x4c, 0x8b, 0x5b, 0x89, 0x66, 0xd8, 0x3e, 0x1c, 0x94, 0x85,
  0xe4, 0xbe, 0xa9, 0x11, 0x2e, 0x54, 0xa5, 0x8a, 0x49, 0xb5, 0xba, 0x5a, 0x13, 0xc6, 0xee, 0xa7,
  0x04, 0x9d, 0x33, 0xef, 0x5a, 0x0a, 0x6f, 0x5f, 0x56, 0x06, 0x8f, 0xfb, 0xc2, 0x19, 0xd2, 0xa3,
  0x19, 0x89, 0x12, 0x3e, 0xd0, 0x32, 0x80, 0xf3, 0xcc, 0xa3, 0xb9, 0xee, 0x03, 0xa0, 0x04, 0x66,
  0x2e, 0x01, 0x81, 0xc5, 0xee, 0x17, 0x19, 0xe5, 0xfa, 0xe5, 0xd5, 0xb4, 0x2a, 0x3c, 0xbf, 0x0a,
  0xff, 0x32, 0x97, 0xeb, 0x33, 0xc1, 0xac, 0xf8, 0x5b, 0xee, 0x4e, 0x0b, 0xe4, 0x38, 0x98, 0x1a,
  0x07, 0xc7, 0x4f, 0x8a, 0x92, 0x2a, 0x67, 0xa9, 0xf7, 0x7b, 0x67, 0x37, 0x5d, 0x5c, 0xb1, 0xbf,
  0x89, 0xd5, 0xd5, 0xf2, 0xe7, 0xd1, 0x6f, 0x95, 0x51, 0x65, 0x6d, 0xdb, 0xca, 0x0c, 0xa1, 0x34,
  0x08, 0x62, 0xef, 0xd9, 0x3e, 0x10, 0x5d, 0x78, 0x9a, 0x1a, 0x7f, 0x27, 0x1e, 0x04, 0xb6, 0xed,
  0xe1, 0x7f, 0xa8, 0x76, 0x75, 0x30, 0x2e, 0x63, 0x67, 0x10, 0x94, 0x24, 0x36, 0x30, 0x14, 0x01
};

uint8_t exp_e[256] = {
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01
};

#endif

