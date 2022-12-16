%ifdef CONFIG
{
  "HostFeatures": ["AVX"],
  "RegData": {
    "RAX": "0x000000004d2fa47f",
    "RBX": "0x0000000067d29af3",
    "RCX": "0x8a6789f27404b890",
    "RDX": "0x00f658ab78236612"
  }
}
%endif

lea rdx, [rel .data]
mov rsi, 0xe0000000

vmovaps xmm1, [rdx + 16 * 0]
vmovaps xmm2, [rdx + 16 * 1]
vmovaps xmm3, [rdx + 16 * 2]
vmovaps xmm4, [rdx + 16 * 3]
vmovaps xmm5, [rdx + 16 * 4]
vmovaps xmm6, [rdx + 16 * 5]
vmovaps xmm7, [rdx + 16 * 6]
vmovaps xmm8, [rdx + 16 * 7]

mov rax, 0
mov [rsi + 8 * 0], rax

vpextrd eax, xmm1, 0
vpextrd ebx, xmm2, 0xFF
vpextrd [rsi + 8 * 0 + 0], xmm3, 2
vpextrd [rsi + 8 * 0 + 4], xmm4, 0xFF
vpextrd [rsi + 8 * 1 + 0], xmm5, 4
vpextrd [rsi + 8 * 1 + 4], xmm6, 5
mov rcx, [rsi + 8 * 0]
mov rdx, [rsi + 8 * 1]

hlt

align 16
; 256bytes of random data
.data:
db 0x7f, 0xa4, 0x2f, 0x4d, 0x25, 0x0f, 0x51, 0x48, 0x86, 0x48, 0x97, 0x3a, 0x31, 0x74, 0x57, 0x2b
db 0x6b, 0xe8, 0x6d, 0x1f, 0xde, 0x56, 0xb5, 0x30, 0x2c, 0x76, 0xae, 0x30, 0xf3, 0x9a, 0xd2, 0x67
db 0x09, 0xad, 0xe8, 0x3d, 0x53, 0xb9, 0x15, 0xb6, 0x90, 0xb8, 0x04, 0x74, 0xa3, 0x72, 0x64, 0xb7
db 0xad, 0x10, 0xf1, 0x72, 0x4c, 0x6b, 0x42, 0x24, 0x67, 0xa5, 0x15, 0xd4, 0xf2, 0x89, 0x67, 0x8a
db 0x12, 0x66, 0x23, 0x78, 0x81, 0xf8, 0x96, 0x89, 0xa9, 0xa2, 0x3c, 0x3d, 0x82, 0x6b, 0xa2, 0x19
db 0xb0, 0x12, 0x97, 0x68, 0xab, 0x58, 0xf6, 0x00, 0x72, 0x19, 0xd2, 0x1e, 0x03, 0x9d, 0x7d, 0xc9
db 0xc8, 0x55, 0xdf, 0x98, 0x22, 0x43, 0x86, 0x1c, 0xcc, 0xe9, 0x1b, 0x89, 0xda, 0xfe, 0x9b, 0xb2
db 0x47, 0x21, 0x0f, 0x71, 0x28, 0xbd, 0xb0, 0x88, 0x38, 0xac, 0xb5, 0x7f, 0x88, 0x5e, 0xe9, 0xc4
db 0xe4, 0x5b, 0x3e, 0xd0, 0x2a, 0x8c, 0xdf, 0xa7, 0xea, 0x95, 0xd3, 0xc2, 0xee, 0xd1, 0x70, 0x6c
db 0x18, 0x77, 0xc1, 0x38, 0x7b, 0xfc, 0xa9, 0x58, 0x92, 0xe8, 0xc6, 0xcd, 0x07, 0x5d, 0x3d, 0x76
db 0xf4, 0x4c, 0x5b, 0x25, 0x7f, 0x9b, 0x02, 0x41, 0x78, 0x39, 0x9e, 0x3e, 0x4c, 0xa2, 0x79, 0xca
db 0x1c, 0xe9, 0xf2, 0x9a, 0xaf, 0x6d, 0xfa, 0x57, 0x10, 0xc7, 0xfd, 0x5f, 0x20, 0x80, 0xf5, 0x65
db 0x3c, 0x77, 0xfb, 0xa8, 0xdf, 0x94, 0x16, 0x4f, 0xc0, 0x78, 0x00, 0x76, 0x03, 0x8c, 0x82, 0x10
db 0x7f, 0x07, 0xe0, 0x02, 0x92, 0xbb, 0xf9, 0x2e, 0xfa, 0x3d, 0x88, 0xc8, 0x24, 0x27, 0xa6, 0x1e
db 0x04, 0x90, 0xf6, 0xf8, 0x76, 0x0a, 0x4c, 0x94, 0xbc, 0xb7, 0x8d, 0x8b, 0xf9, 0x65, 0xf5, 0x07
db 0x7f, 0xc1, 0x37, 0x78, 0xa1, 0x1f, 0xc4, 0x10, 0x6c, 0x29, 0x5e, 0x7e, 0x32, 0x24, 0x92, 0x09
