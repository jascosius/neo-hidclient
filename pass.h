//simulate this characters when pressing RStrg+Print
//for example this could be your device password
//look to the chars table in hidclient.c to find the right values to use here

#define ARRAY 4
unsigned char pass[ARRAY][2] = {{0x00,0x1E},{0x00,0x1F},{0x00,0x20},{0x00,0x28}};
