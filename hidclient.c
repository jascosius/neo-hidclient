/*
 * hidclient - A Bluetooth HID client device emulation
 *
 *		A bluetooth/bluez software emulating a bluetooth mouse/keyboard
 *		combination device - use it to transmit mouse movements and
 *		keyboard keystrokes from a Linux box to any other BTHID enabled
 *		computer or compatible machine
 * 
 * 
 * Implementation
 * 2004-2006	by Anselm Martin Hoffmeister
 * 		   <stockholm(at)users(period)sourceforge(period)net>
 * 2004/2005	Implementation for the GPLed Nokia-supported Affix Bluetooth
 * 		stack as a practical work at
 * 		Rheinische Friedrich-Wilhelms-UniversitÃ€t, Bonn, Germany
 * 2006		Software ported to Bluez, several code cleanups
 * 2006-07-25	First public release
 * 
 * Updates
 * 2012-02-10	by Peter G
 *		Updated to work with current distro (Lubuntu 11.10)
 *		EDIT FILE /etc/bluetooth/main.conf
 *		to include:	
 *			DisablePlugins = network,input,hal,pnat
 *		AMH: Just disable input might be good enough.
 *		recomended to change:
 *			Class = 0x000540
 *		AMH: This leads to the device being found as "Keyboard".
 *		Some devices might ignore non-0x540 input devices
 *		before starting, also execute the following commands
 *			hciconfig hci0 class 0x000540
 *			# AMH: Should be optional if Class= set (above)
 *			hciconfig hci0 name \'Bluetooth Keyboard\'
 *			# AMH: Optional: Name will be seen by other BTs
 *			hciconfig hci0 sspmode 0
 *			# AMH: Optional: Disables simple pairing mode
 *			sdptool del 0x10000
 *			sdptool del 0x10001
 *			sdptool del 0x10002
 *			sdptool del 0x10003
 *			sdptool del 0x10004
 *			sdptool del 0x10005
 *			sdptool del 0x10006
 *			sdptool del 0x10007
 *			sdptool del 0x10008
 *			# This removes any non-HID SDP entries.
 *			# Might help if other devices only like
 *			# single-function Bluetooth devices
 *			# Not strictly required though.
 * 2012-07-26	Several small updates necessary to work on
 *		Ubuntu 12.04 LTS on amd64
 *		Added -e, -l, -x
 * 2012-07-28	Add support for FIFO operation (-f/filename)
 * 
 * Dependency:	Needs libbluetooth (from bluez)
 *
 * Usage:	hidclient [-h|-?|--help] [-s|--skipsdp]
 * 		Start hidclient. -h will display usage information.
 *		-e<NUM> asks hidclient to ONLY use Input device #NUM
 *		-f<FILENAME> will not read event devices, but create a
 *		   fifo on <FILENAME> and read input_event data blocks
 *		   from there
 *		-l will list input devices available
 *		-x will try to remove the "grabbed" input devices from
 *		   the local X11 server, if possible
 * 		-s will disable SDP registration (which only makes sense
 * 		when debugging as most counterparts require SDP to work)
 * Tip:		Use "openvt" along with hidclient so that keystrokes and
 * 		mouse events captured will have no negative impact on the
 * 		local machine (except Ctrl+Alt+[Fn/Entf/Pause]).
 * 		Run
 * 		openvt -s -w hidclient
 * 		to run hidclient on a virtual text mode console for itself.
 * Alternative:	Use "hidclient" in a X11 session after giving the active
 *		user read permissions on the /dev/input/event<NUM> devices
 *		you intend to use. With the help of -x (and possibly -e<NUM>)
 *		this should simply disattach input devices from the local
 *		machine while hidclient is running (and hopefully, reattach
 *		them afterwards, of course).
 * 		
 * License:
 *		This program is free software; you can redistribute it and/or
 *		modify it under the terms of the GNU General Public License as
 *		published by the Free Software Foundation;
 *		strictly version 2 only.
 *
 *		This program is distributed in the hope that it will be useful,
 *		but WITHOUT ANY WARRANTY; without even the implied warranty of
 *		MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *		GNU General Public License for more details.
 *
 *		You should have received a copy of the GNU General Public
 *		License	along with this program; if not, write to the
 *		Free Software Foundation, Inc., 51 Franklin St, Fifth Floor,
 *		Boston, MA  02110-1301  USA
 */

/*
 * Changed by Marius Rasch to use for provide the neo-layout
 * (http://neo-layout.org/) to devices that doesn't support it.
 * Because as specially iOS-Devices doesn't support it, the German Apple
 * Keyboard Layout is assumed at the client.
 *
 * A pressed key will be simulated as an other one to send the right
 * character in the neo-layout.
 *
 * When uses the -x parameter press PRINT to change between input for
 * the computer and input for the device.
 *
 * Press LCtrg+PRINT to stop the program.
 * Press RCtrg+PRINT to send a string defined in pass.h.
 */


//***************** Include files
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stropts.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <linux/input.h>
#include <bluetooth/bluetooth.h>
#include <bluetooth/hci.h>
#include <bluetooth/hci_lib.h>
#include <bluetooth/l2cap.h>
#include <bluetooth/sdp.h>
#include <bluetooth/sdp_lib.h>
#include "pass.h"

//***************** Static definitions
// Where to find event devices (that must be readable by current user)
// "%d" to be filled in, opening several devices, see below
#define	EVDEVNAME	"/dev/input/event%d"

// Maximally, read MAXEVDEVS event devices simultaneously
#define	MAXEVDEVS 16

// Bluetooth "ports" (PSMs) for HID usage, standardized to be 17 and 19 resp.
// In theory you could use different ports, but several implementations seem
// to ignore the port info in the SDP records and always use 17 and 19. YMMV.
#define	PSMHIDCTL	0x11
#define	PSMHIDINT	0x13

// Information to be submitted to the SDP server, as service description
#define	HIDINFO_NAME	"Bluez virtual Mouse and Keyboard"
#define	HIDINFO_PROV	"Anselm Martin Hoffmeister (GPL v2)"
#define	HIDINFO_DESC	"Keyboard"

// These numbers must also be used in the HID descriptor binary file
#define	REPORTID_MOUSE	1
#define	REPORTID_KEYBD	2

// Fixed SDP record, corresponding to data structures below. Explanation
// is in separate text file. No reason to change this if you do not want
// to fiddle with the data sent over the BT connection as well.
#define SDPRECORD	"\x05\x01\x09\x02\xA1\x01\x85\x01\x09\x01\xA1\x00" \
			"\x05\x09\x19\x01\x29\x03\x15\x00\x25\x01\x75\x01" \
			"\x95\x03\x81\x02\x75\x05\x95\x01\x81\x01\x05\x01" \
			"\x09\x30\x09\x31\x09\x38\x15\x81\x25\x7F\x75\x08" \
			"\x95\x02\x81\x06\xC0\xC0\x05\x01\x09\x06\xA1\x01" \
			"\x85\x02\xA1\x00\x05\x07\x19\xE0\x29\xE7\x15\x00" \
			"\x25\x01\x75\x01\x95\x08\x81\x02\x95\x08\x75\x08" \
			"\x15\x00\x25\x65\x05\x07\x19\x00\x29\x65\x81\x00" \
			"\xC0\xC0"
#define SDPRECORD_BYTES	98

//***************** Function prototypes
int		dosdpregistration(void);
void		sdpunregister(unsigned int);
static void	add_lang_attr(sdp_record_t *r);
int		btbind(int sockfd, unsigned short port);
int		initevents(int,int);
void		closeevents(void);
int		initfifo(char *);
void		closefifo(void);
void		cleanup_stdin(void);
int		add_filedescriptors(fd_set*);
int		parse_events(fd_set*,int);
void		showhelp(void);
void		onsignal(int);

//***************** Data structures
// Mouse HID report, as sent over the wire:
struct hidrep_mouse_t
{
	unsigned char	btcode;	// Fixed value for "Data Frame": 0xA1
	unsigned char	rep_id; // Will be set to REPORTID_MOUSE for "mouse"
	unsigned char	button;	// bits 0..2 for left,right,middle, others 0
	signed   char	axis_x; // relative movement in pixels, left/right
	signed   char	axis_y; // dito, up/down
	signed   char	axis_z; // Used for the scroll wheel (?)
} __attribute((packed));
// Keyboard HID report, as sent over the wire:
struct hidrep_keyb_t
{
	unsigned char	btcode; // Fixed value for "Data Frame": 0xA1
	unsigned char	rep_id; // Will be set to REPORTID_KEYBD for "keyboard"
	unsigned char	modify; // Modifier keys (shift, alt, the like)
	unsigned char	key[8]; // Currently pressed keys, max 8 at once
} __attribute((packed));

//***************** Global variables
char		prepareshutdown	 = 0;	// Set if shutdown was requested
int		eventdevs[MAXEVDEVS];	// file descriptors
int		x11handles[MAXEVDEVS];
char		mousebuttons	 = 0;	// storage for button status
int 		modifierkeys	 = 0;	// and for shift/ctrl/alt... status
char		pressedkey[8]	 = { 0, 0, 0, 0,  0, 0, 0, 0 };
char		connectionok	 = 0;
uint32_t	sdphandle	 = 0;	// To be used to "unregister" on exit
int		debugevents      = 0;	// bitmask for debugging event data

char	*result = NULL;

unsigned char stop_writing = 0; //stop writing on computer when writing on external device
unsigned char on = 0; //is "stop writing" actually on or off
unsigned char id = 0; //id of keyboard to stop writing

extern unsigned char pass[ARRAY][2];

/* Defines the keys to press to get the neo-char
 * Client has to use the German apple keyboard layout
 * 
 * every line is for one key code and specifies the 6 neo-layers for this key
 * in every tuple the first entry is the modifier keys to press
 * the second entry is the key to press
 *
 * modifier LShift = 0x02, LAlt = 0x04, LShift+LAlt = (0x02 & 0x04) = 0x06
 *
 * For example:
 * chars[4] is the entry used, when the key with code 4 is pressed
 * this is the A on an US and DE Layout keyboard
 * on layer 1 of neo this is an u
 * you get an u on the German apple keyboard by pressing key 0x18 and no modifier
 * on layer 2 of neo this is an U
 * you get an U on the German apple keyboard by pressing key 0x18 and shift (0x02)
 * on layer 3 of neo this is an \
 * you get an \ on the German apple keyboard by pressing key 0x24 and shift+alt (0x06)
 */
unsigned char chars[100][6][2] = {  
  {{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}},
  {{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}},
  {{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}},
  {{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}},
  {{0x00,0x18},{0x02,0x18},{0x06,0x24},{0x00,0x4A},{0x00,0x00},{0x00,0x00}}, // 4 0x04 - US: A         , DE: A         , Layer 1: u         , Layer 2: U         , Layer 3: \         , Layer 4: Pos1
  {{0x00,0x1C},{0x02,0x1C},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, // 5 0x05 - US: B         , DE: B         , Layer 1: z         , Layer 2: Z         , Layer 3: `         , Layer 4: 
  {{0x00,0x34},{0x02,0x34},{0x04,0x24},{0x00,0x49},{0x00,0x00},{0x00,0x00}}, // 6 0x06 - US: C         , DE: C         , Layer 1: ä         , Layer 2: Ä         , Layer 3: |         , Layer 4: Einfügen
  {{0x00,0x04},{0x02,0x04},{0x04,0x25},{0x00,0x51},{0x00,0x00},{0x00,0x00}}, // 7 0x07 - US: D         , DE: D         , Layer 1: a         , Layer 2: A         , Layer 3: {         , Layer 4: Untere Pf.
  {{0x00,0x0F},{0x02,0x0F},{0x04,0x22},{0x00,0x52},{0x00,0x00},{0x00,0x00}}, // 8 0x08 - US: E         , DE: E         , Layer 1: l         , Layer 2: L         , Layer 3: [         , Layer 4: Obere Pf.
  {{0x00,0x08},{0x02,0x08},{0x04,0x26},{0x00,0x4F},{0x00,0x00},{0x00,0x00}}, // 9 0x09 - US: F         , DE: F         , Layer 1: e         , Layer 2: E         , Layer 3: }         , Layer 4: Rechte Pf.
  {{0x00,0x12},{0x02,0x12},{0x02,0x30},{0x00,0x4D},{0x00,0x00},{0x00,0x00}}, //10 0x0A - US: G         , DE: G         , Layer 1: o         , Layer 2: O         , Layer 3: *         , Layer 4: Ende
  {{0x00,0x16},{0x02,0x16},{0x02,0x2D},{0x04,0x2D},{0x00,0x00},{0x00,0x00}}, //11 0x0B - US: H         , DE: H         , Layer 1: s         , Layer 2: S         , Layer 3: ?         , Layer 4: ¿
  {{0x00,0x0A},{0x02,0x0A},{0x02,0x35},{0x00,0x25},{0x00,0x00},{0x00,0x00}}, //12 0x0C - US: I         , DE: I         , Layer 1: g         , Layer 2: G         , Layer 3: >         , Layer 4: 8
  {{0x00,0x11},{0x02,0x11},{0x02,0x25},{0x00,0x21},{0x00,0x00},{0x00,0x00}}, //13 0x0D - US: J         , DE: J         , Layer 1: n         , Layer 2: N         , Layer 3: (         , Layer 4: 4
  {{0x00,0x15},{0x02,0x15},{0x02,0x26},{0x00,0x22},{0x00,0x00},{0x00,0x00}}, //14 0x0E - US: K         , DE: K         , Layer 1: r         , Layer 2: R         , Layer 3: )         , Layer 4: 5
  {{0x00,0x17},{0x02,0x17},{0x00,0x38},{0x00,0x23},{0x00,0x00},{0x00,0x00}}, //15 0x0F - US: L         , DE: L         , Layer 1: t         , Layer 2: T         , Layer 3: -         , Layer 4: 6
  {{0x00,0x10},{0x02,0x10},{0x02,0x22},{0x00,0x1E},{0x00,0x00},{0x00,0x00}}, //16 0x10 - US: M         , DE: M         , Layer 1: m         , Layer 2: M         , Layer 3: %         , Layer 4: 1         , Layer 5: μ
  {{0x00,0x05},{0x02,0x05},{0x00,0x30},{0x02,0x37},{0x00,0x00},{0x00,0x00}}, //17 0x11 - US: N         , DE: N         , Layer 1: b         , Layer 2: B         , Layer 3: +         , Layer 4: :
  {{0x00,0x09},{0x02,0x09},{0x02,0x27},{0x00,0x26},{0x00,0x00},{0x00,0x00}}, //18 0x12 - US: O         , DE: O         , Layer 1: f         , Layer 2: F         , Layer 3: =         , Layer 4: 9
  {{0x00,0x14},{0x02,0x14},{0x02,0x23},{0x00,0x30},{0x00,0x00},{0x00,0x00}}, //19 0x13 - US: P         , DE: P         , Layer 1: q         , Layer 2: Q         , Layer 3: &         , Layer 4: +
  {{0x00,0x1B},{0x02,0x1B},{0x04,0x37},{0x00,0x4B},{0x00,0x00},{0x00,0x00}}, //20 0x14 - US: Q         , DE: Q         , Layer 1: x         , Layer 2: X         , Layer 3: …         , Layer 4: Bild hoch
  {{0x00,0x06},{0x02,0x06},{0x04,0x23},{0x00,0x4C},{0x00,0x00},{0x00,0x00}}, //21 0x15 - US: R         , DE: R         , Layer 1: c         , Layer 2: C         , Layer 3: ]         , Layer 4: Entfernen
  {{0x00,0x0C},{0x02,0x0C},{0x02,0x24},{0x00,0x50},{0x00,0x00},{0x00,0x00}}, //22 0x16 - US: S         , DE: S         , Layer 1: i         , Layer 2: I         , Layer 3: /         , Layer 4: Linke Pf.
  {{0x00,0x1A},{0x02,0x1A},{0x00,0x00},{0x00,0x4E},{0x00,0x00},{0x00,0x00}}, //23 0x17 - US: T         , DE: T         , Layer 1: w         , Layer 2: W         , Layer 3: ^         , Layer 4: Bild runt.
  {{0x00,0x0B},{0x02,0x0B},{0x00,0x35},{0x00,0x24},{0x00,0x00},{0x00,0x00}}, //24 0x18 - US: U         , DE: U         , Layer 1: h         , Layer 2: H         , Layer 3: <         , Layer 4: 7
  {{0x00,0x13},{0x02,0x13},{0x04,0x11},{0x00,0x28},{0x00,0x00},{0x00,0x00}}, //25 0x19 - US: V         , DE: V         , Layer 1: p         , Layer 2: P         , Layer 3: ~         , Layer 4: Enter
  {{0x00,0x19},{0x02,0x19},{0x02,0x38},{0x00,0x2A},{0x00,0x00},{0x00,0x00}}, //26 0x1A - US: W         , DE: W         , Layer 1: v         , Layer 2: V         , Layer 3: _         , Layer 4: Löschen
  {{0x00,0x33},{0x02,0x33},{0x02,0x21},{0x00,0x2B},{0x00,0x00},{0x00,0x00}}, //27 0x1B - US: X         , DE: X         , Layer 1: ö         , Layer 2: Ö         , Layer 3: $         , Layer 4: Tab
  {{0x00,0x0E},{0x02,0x0E},{0x02,0x1E},{0x04,0x1E},{0x00,0x00},{0x00,0x00}}, //28 0x1C - US: Y         , DE: Z         , Layer 1: k         , Layer 2: K         , Layer 3: !         , Layer 4: ¡
  {{0x00,0x2F},{0x02,0x2F},{0x00,0x31},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //29 0x1D - US: Z         , DE: Y         , Layer 1: ü         , Layer 2: Ü         , Layer 3: #         , Layer 4: 
  {{0x00,0x1E},{0x06,0x2F},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //30 0x1E - US: 1         , DE: 1         , Layer 1: 1         , Layer 2: °         , Layer 3: ¹         , Layer 4:
  {{0x00,0x1F},{0x02,0x20},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //31 0x1F - US: 2         , DE: 2         , Layer 1: 2         , Layer 2: §         , Layer 3: ²         , Layer 4:
  {{0x00,0x20},{0x04,0x07},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //32 0x20 - US: 3         , DE: 3         , Layer 1: 3         , Layer 2:           , Layer 3: ³         , Layer 4: 
  {{0x00,0x21},{0x06,0x14},{0x06,0x11},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //33 0x21 - US: 4         , DE: 4         , Layer 1: 4         , Layer 2: »         , Layer 3: ›         , Layer 4: 
  {{0x00,0x22},{0x04,0x14},{0x06,0x05},{0x06,0x26},{0x00,0x00},{0x00,0x00}}, //34 0x22 - US: 5         , DE: 5         , Layer 1: 5         , Layer 2: «         , Layer 3: ‹         , Layer 4: ·
  {{0x00,0x23},{0x02,0x21},{0x04,0x21},{0x06,0x21},{0x00,0x00},{0x00,0x00}}, //35 0x23 - US: 6         , DE: 6         , Layer 1: 6         , Layer 2: $         , Layer 3: ¢         , Layer 4: £
  {{0x00,0x24},{0x04,0x08},{0x04,0x1D},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //36 0x24 - US: 7         , DE: 7         , Layer 1: 7         , Layer 2: €         , Layer 3: ¥         , Layer 4: 
  {{0x00,0x25},{0x06,0x1A},{0x04,0x16},{0x00,0x2B},{0x00,0x00},{0x00,0x00}}, //37 0x25 - US: 8         , DE: 8         , Layer 1: 8         , Layer 2: „         , Layer 3: ‚         , Layer 4: Tab
  {{0x00,0x26},{0x04,0x1F},{0x04,0x31},{0x02,0x24},{0x00,0x00},{0x00,0x00}}, //38 0x26 - US: 9         , DE: 9         , Layer 1: 9         , Layer 2: “         , Layer 3: ‘         , Layer 4: /
  {{0x00,0x27},{0x06,0x1F},{0x00,0x00},{0x02,0x30},{0x00,0x00},{0x00,0x00}}, //39 0x27 - US: 0         , DE: 0         , Layer 1: 0         , Layer 2: ”         , Layer 3: ’         , Layer 4: *
  {{0x00,0x28},{0x02,0x28},{0x00,0x28},{0x04,0x28},{0x00,0x28},{0x00,0x28}}, //40 0x28 - US: ENTER     , DE: Enter     , Layer 1: Enter     , Layer 2: Enter     , Layer 3: Enter     , Layer 4: Enter
  {{0x00,0x29},{0x00,0x29},{0x00,0x29},{0x00,0x29},{0x00,0x29},{0x00,0x29}}, //41 0x29 - US: ESC       , DE: Escape    , Layer 1: Escape    , Layer 2: Escape    , Layer 3: Escape    , Layer 4: Escape
  {{0x00,0x2A},{0x00,0x2A},{0x00,0x2A},{0x00,0x2A},{0x00,0x2A},{0x00,0x2A}}, //42 0x2A - US: BACKSPACE , DE: Löschen   , Layer 1: Löschen   , Layer 2: Löschen   , Layer 3: Löschen   , Layer 4: Löschen
  {{0x00,0x2B},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //43 0x2B - US: TAB       , DE: Tab       , Layer 1: Tab       , Layer 2:           , Layer 3:           , Layer 4: 
  {{0x00,0x2C},{0x02,0x2C},{0x00,0x2C},{0x04,0x27},{0x00,0x00},{0x00,0x00}}, //44 0x2C - US: SPACE     , DE: Leerzei.  , Layer 1: Leerzei.  , Layer 2: Leerzei.  , Layer 3: Leerzei.  , Layer 4: 0
  {{0x00,0x38},{0x06,0x38},{0x00,0x00},{0x00,0x38},{0x00,0x00},{0x00,0x00}}, //45 0x2D - US: MINUS     , DE: ß         , Layer 1: -         , Layer 2:           , Layer 3:           , Layer 4: -
  {{0x02,0x2E},{0x02,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //46 0x2E - US: EQUAL     , DE: Akzent    , Layer 1: `         , Layer 2:           , Layer 3:           , Layer 4: 
  {{0x00,0x2D},{0x00,0x00},{0x00,0x00},{0x04,0x38},{0x00,0x00},{0x00,0x00}}, //47 0x2F - US: LEFTBRACE , DE: Ü         , Layer 1: ß         , Layer 2:           , Layer 3:           , Layer 4: −
  {{0x00,0x2E},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //48 0x30 - US: RIGHTBRACE, DE: Plus      , Layer 1: ´         , Layer 2:           , Layer 3:           , Layer 4: 
  {{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //49 0x31 - US: BACKSLASH , DE: Raute     , Mod 3 
  {{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //50 0x32 - US: 102ND     , DE: spitze K. , Mod 4
  {{0x00,0x07},{0x02,0x07},{0x02,0x37},{0x00,0x36},{0x00,0x00},{0x00,0x00}}, //51 0x33 - US: SEMICOLON , DE: Ö         , Layer 1: d         , Layer 2: D         , Layer 3: :         , Layer 4: ,
  {{0x00,0x1D},{0x02,0x1D},{0x04,0x0F},{0x00,0x37},{0x00,0x00},{0x00,0x00}}, //52 0x34 - US: APOSTROPHE, DE: Ä         , Layer 1: y         , Layer 2: Y         , Layer 3: @         , Layer 4: .
  {{0x06,0x23},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //53 0x35 - US: GRAVE     , DE: Zirkumflex, Layer 1: ^         , Layer 2:           , Layer 3:           , Layer 4: 
  {{0x00,0x36},{0x04,0x38},{0x02,0x1F},{0x00,0x1F},{0x00,0x00},{0x00,0x00}}, //54 0x36 - US: COMMA     , DE: Komma     , Layer 1: ,         , Layer 2: –         , Layer 3: "         , Layer 4: 2
  {{0x00,0x37},{0x04,0x2F},{0x02,0x31},{0x00,0x20},{0x00,0x00},{0x00,0x00}}, //55 0x37 - US: DOT       , DE: Punkt     , Layer 1: .         , Layer 2: •         , Layer 3: '         , Layer 4: 3
  {{0x00,0x0D},{0x02,0x0D},{0x02,0x36},{0x02,0x36},{0x00,0x00},{0x00,0x00}}, //56 0x38 - US: SLASH     , DE: Bindestr. , Layer 1: j         , Layer 2: J         , Layer 3: ;         , Layer 4: ;
  {{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //57 0x39 - US: CAPSLOCK  , DE: Umschalt  , Mod 3 
  {{0x00,0x3A},{0x00,0x3A},{0x00,0x3A},{0x00,0x3A},{0x00,0x3A},{0x00,0x3A}}, //58 0x3A - US: F1        , DE: F1        , Layer 1: F1        , Layer 2: F1        , Layer 3: F1        , Layer 4: F1
  {{0x00,0x3B},{0x00,0x3B},{0x00,0x3B},{0x00,0x3B},{0x00,0x3B},{0x00,0x3B}}, //59 0x3B - US: F2        , DE: F2        , Layer 1: F2        , Layer 2: F2        , Layer 3: F2        , Layer 4: F2
  {{0x00,0x3C},{0x00,0x3C},{0x00,0x3C},{0x00,0x3C},{0x00,0x3C},{0x00,0x3C}}, //60 0x3C - US: F3        , DE: F3        , Layer 1: F3        , Layer 2: F3        , Layer 3: F3        , Layer 4: F3
  {{0x00,0x3D},{0x00,0x3D},{0x00,0x3D},{0x00,0x3D},{0x00,0x3D},{0x00,0x3D}}, //61 0x3D - US: F4        , DE: F4        , Layer 1: F4        , Layer 2: F4        , Layer 3: F4        , Layer 4: F4
  {{0x00,0x3E},{0x00,0x3E},{0x00,0x3E},{0x00,0x3E},{0x00,0x3E},{0x00,0x3E}}, //62 0x3E - US: F5        , DE: F5        , Layer 1: F5        , Layer 2: F5        , Layer 3: F5        , Layer 4: F5
  {{0x00,0x3F},{0x00,0x3F},{0x00,0x3F},{0x00,0x3F},{0x00,0x3F},{0x00,0x3F}}, //63 0x3F - US: F6        , DE: F6        , Layer 1: F6        , Layer 2: F6        , Layer 3: F6        , Layer 4: F6
  {{0x00,0x40},{0x00,0x40},{0x00,0x40},{0x00,0x40},{0x00,0x40},{0x00,0x40}}, //64 0x40 - US: F7        , DE: F7        , Layer 1: F7        , Layer 2: F7        , Layer 3: F7        , Layer 4: F7
  {{0x00,0x41},{0x00,0x41},{0x00,0x41},{0x00,0x41},{0x00,0x41},{0x00,0x41}}, //65 0x41 - US: F8        , DE: F8        , Layer 1: F8        , Layer 2: F8        , Layer 3: F8        , Layer 4: F8
  {{0x00,0x42},{0x00,0x42},{0x00,0x42},{0x00,0x42},{0x00,0x42},{0x00,0x42}}, //66 0x42 - US: F9        , DE: F9        , Layer 1: F9        , Layer 2: F9        , Layer 3: F9        , Layer 4: F9
  {{0x00,0x43},{0x00,0x43},{0x00,0x43},{0x00,0x43},{0x00,0x43},{0x00,0x43}}, //67 0x43 - US: F10       , DE: F10       , Layer 1: F10       , Layer 2: F10       , Layer 3: F10       , Layer 4: F10
  {{0x00,0x44},{0x00,0x44},{0x00,0x44},{0x00,0x44},{0x00,0x44},{0x00,0x44}}, //68 0x44 - US: F11       , DE: F11       , Layer 1: F11       , Layer 2: F11       , Layer 3: F11       , Layer 4: F11
  {{0x00,0x45},{0x00,0x45},{0x00,0x45},{0x00,0x45},{0x00,0x45},{0x00,0x45}}, //69 0x45 - US: F12       , DE: F12       , Layer 1: F12       , Layer 2: F12       , Layer 3: F12       , Layer 4: F12
  {{0x00,0x46},{0x00,0x46},{0x00,0x46},{0x00,0x46},{0x00,0x46},{0x00,0x46}}, //70 0x46 - US: PRINT     , DE: Drucken   , Layer 1: Drucken   , Layer 2: Drucken   , Layer 3: Drucken   , Layer 4: Drucken
  {{0x00,0x47},{0x00,0x47},{0x00,0x47},{0x00,0x47},{0x00,0x47},{0x00,0x47}}, //71 0x47 - US: SCROLLLOCK, DE: Scrollen  , Layer 1: Scrollen  , Layer 2: Scrollen  , Layer 3: Scrollen  , Layer 4: Scrollen
  {{0x00,0x48},{0x00,0x48},{0x00,0x48},{0x00,0x48},{0x00,0x48},{0x00,0x48}}, //72 0x48 - US: PAUSE     , DE: Pause     , Layer 1: Pause     , Layer 2: Pause     , Layer 3: Pause     , Layer 4: Pause
  {{0x00,0x49},{0x00,0x49},{0x00,0x49},{0x00,0x49},{0x00,0x49},{0x00,0x49}}, //73 0x49 - US: INSERT    , DE: Einfügen  , Layer 1: Einfügen  , Layer 2: Einfügen  , Layer 3: Einfügen  , Layer 4: Einfügen
  {{0x00,0x4A},{0x00,0x4A},{0x00,0x4A},{0x00,0x4A},{0x00,0x4A},{0x00,0x4A}}, //74 0x4A - US: HOME      , DE: Pos1      , Layer 1: Pos1      , Layer 2: Pos1      , Layer 3: Pos1      , Layer 4: Pos1
  {{0x00,0x4B},{0x00,0x4B},{0x00,0x4B},{0x00,0x4B},{0x00,0x4B},{0x00,0x4B}}, //75 0x4B - US: PAGEUP    , DE: Bild hoch , Layer 1: Bild hoch , Layer 2: Bild hoch , Layer 3: Bild hoch , Layer 4: Bild hoch
  {{0x00,0x4C},{0x00,0x4C},{0x00,0x4C},{0x00,0x4C},{0x00,0x4C},{0x00,0x4C}}, //76 0x4C - US: DELETE    , DE: Entfernen , Layer 1: Entfernen , Layer 2: Entfernen , Layer 3: Entfernen , Layer 4: Entfernen
  {{0x00,0x4D},{0x00,0x4D},{0x00,0x4D},{0x00,0x4D},{0x00,0x4D},{0x00,0x4D}}, //77 0x4D - US: END       , DE: Ende      , Layer 1: Ende      , Layer 2: Ende      , Layer 3: Ende      , Layer 4: Ende
  {{0x00,0x4E},{0x00,0x4E},{0x00,0x4E},{0x00,0x4E},{0x00,0x4E},{0x00,0x4E}}, //78 0x4E - US: PAGEDOWN  , DE: Bild runt., Layer 1: Bild runt., Layer 2: Bild runt., Layer 3: Bild runt., Layer 4: Bild runt.
  {{0x00,0x4F},{0x00,0x4F},{0x00,0x4F},{0x00,0x4F},{0x00,0x4F},{0x00,0x4F}}, //79 0x4F - US: RIGHT     , DE: Rechte Pf., Layer 1: Rechte Pf., Layer 2: Rechte Pf., Layer 3: Rechte Pf., Layer 4: Rechte Pf.
  {{0x00,0x50},{0x00,0x50},{0x00,0x50},{0x00,0x50},{0x00,0x50},{0x00,0x50}}, //80 0x50 - US: LEFT      , DE: Linke Pf. , Layer 1: Linke Pf. , Layer 2: Linke Pf. , Layer 3: Linke Pf. , Layer 4: Linke Pf.
  {{0x00,0x51},{0x00,0x51},{0x00,0x51},{0x00,0x51},{0x00,0x51},{0x00,0x51}}, //81 0x51 - US: DOWN      , DE: Untere Pf., Layer 1: Untere Pf., Layer 2: Untere Pf., Layer 3: Untere Pf., Layer 4: Untere Pf.
  {{0x00,0x52},{0x00,0x52},{0x00,0x52},{0x00,0x52},{0x00,0x52},{0x00,0x52}}, //82 0x52 - US: UP        , DE: Obere Pf. , Layer 1: Obere Pf. , Layer 2: Obere Pf. , Layer 3: Obere Pf. , Layer 4: Obere Pf.
  {{0x00,0x2B},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //83 0x53 - US: NUMLOCK   , DE: Numlock   , Layer 1: Tab       , Layer 2:           , Layer 3:           , Layer 4:
  {{0x02,0x24},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //84 0x54 - US: KPSLASH   , DE: NB Slash  , Layer 1: /         , Layer 2:           , Layer 3:           , Layer 4: 
  {{0x02,0x30},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //85 0x55 - US: KPASTERISK, DE: NB Stern  , Layer 1: *         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x38},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //86 0x56 - US: KPMINUS   , DE: NB Minus  , Layer 1: -         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x30},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //87 0x57 - US: KPPLUS    , DE: NB Plus   , Layer 1: +         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x28},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //88 0x58 - US: KPENTER   , DE: NB Enter  , Layer 1: Enter     , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x1E},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //89 0x59 - US: KP1       , DE: NB 1      , Layer 1: 1         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x1F},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //90 0x5A - US: KP2       , DE: NB 2      , Layer 1: 2         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x20},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //91 0x5B - US: KP3       , DE: NB 3      , Layer 1: 3         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x21},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //92 0x5C - US: KP4       , DE: NB 4      , Layer 1: 4         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x22},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //93 0x5D - US: KP5       , DE: NB 5      , Layer 1: 5         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x23},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //94 0x5E - US: KP6       , DE: NB 6      , Layer 1: 6         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x24},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //95 0x5F - US: KP7       , DE: NB 7      , Layer 1: 7         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x25},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //96 0x60 - US: KP8       , DE: NB 8      , Layer 1: 8         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x26},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //97 0x61 - US: KP9       , DE: NB 9      , Layer 1: 9         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x27},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}, //98 0x62 - US: KP0       , DE: NB 0      , Layer 1: 0         , Layer 2:           , Layer 3:           , Layer 4:
  {{0x00,0x36},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00},{0x00,0x00}}  //99 0x63 - US: KPDOT     , DE: NB Punkt  , Layer 1: ,         , Layer 2:           , Layer 3:           , Layer 4:
};



//***************** Implementation
/* 
 * Taken from bluetooth library because of suspicious memory allocation
 * THIS IS A HACK that appears to work, and did not need to look into how it works
 * SHOULD BE FIXED AND FIX BACKPORTED TO BLUEZ
 */
sdp_data_t *sdp_seq_alloc_with_length(void **dtds, void **values, int *length,
								int len)
{
	sdp_data_t *curr = NULL, *seq = NULL;
	int i;
	int totall = 1024;

	for (i = 0; i < len; i++) {
		sdp_data_t *data;
		int8_t dtd = *(uint8_t *) dtds[i];


		if (dtd >= SDP_SEQ8 && dtd <= SDP_ALT32) {
			data = (sdp_data_t *) values[i]; }
		else {
			data = sdp_data_alloc_with_length(dtd, values[i], length[i]); }

		if (!data)
			return NULL;

		if (curr)
			curr->next = data;
		else
			seq = data;

		curr = data;
		totall +=  length[i] + sizeof *seq; /* no idea what this should really be */
	}
/*
 * Here we had a reference here to a non-existing array member. Changed it something that
 * appears to be large enough BUT author has no idea what it really should be
 */
//  fprintf ( stderr, "length[%d]): %d, totall: %d\n", i, length[i], totall);

	return sdp_data_alloc_with_length(SDP_SEQ8, seq, totall);
}

/*
 * dosdpregistration -	Care for the proper SDP record sent to the "sdpd"
 *			so that other BT devices can discover the HID service
 * Parameters: none; Return value: 0 = OK, >0 = failure
 */
int	dosdpregistration ( void )
{
	sdp_record_t	record;
	sdp_session_t	*session;
        sdp_list_t	*svclass_id,
			*pfseq,
			*apseq,
			*root;
	uuid_t		root_uuid,
			hidkb_uuid,
			l2cap_uuid,
			hidp_uuid;
        sdp_profile_desc_t	profile[1];
        sdp_list_t	*aproto,
			*proto[3];
	sdp_data_t	*psm,
			*lang_lst,
			*lang_lst2,
			*hid_spec_lst,
			*hid_spec_lst2;
        void		*dtds[2],
			*values[2],
			*dtds2[2],
			*values2[2];
        int		i,
			leng[2];
        uint8_t		dtd=SDP_UINT16,
			dtd2=SDP_UINT8,
			dtd_data=SDP_TEXT_STR8,
			hid_spec_type=0x22;
        uint16_t	hid_attr_lang[]={0x409, 0x100},
			ctrl=PSMHIDCTL,
			intr=PSMHIDINT,
			hid_attr[]={0x100, 0x111, 0x40, 0x00, 0x01, 0x01},
			// Assigned to SDP 0x200...0x205 - see HID SPEC for
			// details. Those values seem to work fine...
			// "it\'s a kind of magic" numbers.
			hid_attr2[]={0x100, 0x0};

	// Connect to SDP server on localhost, to publish service information
	session = sdp_connect ( BDADDR_ANY, BDADDR_LOCAL, 0 );
	if ( ! session )
	{
		fprintf ( stderr, "Failed to connect to SDP server: %s\n",
				strerror ( errno ) );
		return	1;
	}
        memset(&record, 0, sizeof(sdp_record_t));
        record.handle = 0xffffffff;
	// With 0xffffffff, we get assigned the first free record >= 0x10000
	// Make HID service visible (add to PUBLIC BROWSE GROUP)
        sdp_uuid16_create(&root_uuid, PUBLIC_BROWSE_GROUP);
        root = sdp_list_append(0, &root_uuid);
        sdp_set_browse_groups(&record, root);
	// Language Information to be added
        add_lang_attr(&record);
	// The descriptor for the keyboard
        sdp_uuid16_create(&hidkb_uuid, HID_SVCLASS_ID);
        svclass_id = sdp_list_append(0, &hidkb_uuid);
        sdp_set_service_classes(&record, svclass_id);
	// And information about the HID profile used
        sdp_uuid16_create(&profile[0].uuid, HIDP_UUID /*HID_PROFILE_ID*/);
        profile[0].version = 0x0100;
        pfseq = sdp_list_append(0, profile);
        sdp_set_profile_descs(&record, pfseq);
	// We are using L2CAP, so add an info about that
        sdp_uuid16_create(&l2cap_uuid, L2CAP_UUID);
        proto[1] = sdp_list_append(0, &l2cap_uuid);
        psm = sdp_data_alloc(SDP_UINT16, &ctrl);
        proto[1] = sdp_list_append(proto[1], psm);
        apseq = sdp_list_append(0, proto[1]);
	// And about our purpose, the HID protocol data transfer
        sdp_uuid16_create(&hidp_uuid, HIDP_UUID);
        proto[2] = sdp_list_append(0, &hidp_uuid);
        apseq = sdp_list_append(apseq, proto[2]);
        aproto = sdp_list_append(0, apseq);
        sdp_set_access_protos(&record, aproto);
        proto[1] = sdp_list_append(0, &l2cap_uuid);
        psm = sdp_data_alloc(SDP_UINT16, &intr);
        proto[1] = sdp_list_append(proto[1], psm);
        apseq = sdp_list_append(0, proto[1]);
        sdp_uuid16_create(&hidp_uuid, HIDP_UUID);
        proto[2] = sdp_list_append(0, &hidp_uuid);
        apseq = sdp_list_append(apseq, proto[2]);
        aproto = sdp_list_append(0, apseq);
        sdp_set_add_access_protos(&record, aproto);
	// Set service name, description
        sdp_set_info_attr(&record, HIDINFO_NAME, HIDINFO_PROV, HIDINFO_DESC);
	// Add a few HID-specifid pieces of information
        // See the HID spec for details what those codes 0x200+something
	// are good for... we send a fixed set of info that seems to work
        sdp_attr_add_new(&record, SDP_ATTR_HID_DEVICE_RELEASE_NUMBER,
                                        SDP_UINT16, &hid_attr[0]); /* Opt */
        sdp_attr_add_new(&record, SDP_ATTR_HID_PARSER_VERSION,
                                        SDP_UINT16, &hid_attr[1]); /* Mand */
        sdp_attr_add_new(&record, SDP_ATTR_HID_DEVICE_SUBCLASS,
                                        SDP_UINT8, &hid_attr[2]); /* Mand */
        sdp_attr_add_new(&record, SDP_ATTR_HID_COUNTRY_CODE,
                                        SDP_UINT8, &hid_attr[3]); /* Mand */
        sdp_attr_add_new(&record, SDP_ATTR_HID_VIRTUAL_CABLE,
                                  SDP_BOOL, &hid_attr[4]); /* Mand */
        sdp_attr_add_new(&record, SDP_ATTR_HID_RECONNECT_INITIATE,
                                  SDP_BOOL, &hid_attr[5]); /* Mand */
	// Add the HID descriptor (describing the virtual device) as code
	// SDP_ATTR_HID_DESCRIPTOR_LIST (0x206 IIRC)
        dtds[0] = &dtd2;
        values[0] = &hid_spec_type;
	dtd_data= SDPRECORD_BYTES <= 255 ? SDP_TEXT_STR8 : SDP_TEXT_STR16 ;
        dtds[1] = &dtd_data;
        values[1] = (uint8_t *) SDPRECORD;
        leng[0] = 0;
        leng[1] = SDPRECORD_BYTES;
        hid_spec_lst = sdp_seq_alloc_with_length(dtds, values, leng, 2);
        hid_spec_lst2 = sdp_data_alloc(SDP_SEQ8, hid_spec_lst);
        sdp_attr_add(&record, SDP_ATTR_HID_DESCRIPTOR_LIST, hid_spec_lst2);
	// and continue adding further data bytes for 0x206+x values
        for (i = 0; i < sizeof(hid_attr_lang) / 2; i++) {
                dtds2[i] = &dtd;
                values2[i] = &hid_attr_lang[i];
        }
        lang_lst = sdp_seq_alloc(dtds2, values2, sizeof(hid_attr_lang) / 2);
        lang_lst2 = sdp_data_alloc(SDP_SEQ8, lang_lst);
        sdp_attr_add(&record, SDP_ATTR_HID_LANG_ID_BASE_LIST, lang_lst2);
	sdp_attr_add_new ( &record, SDP_ATTR_HID_PROFILE_VERSION,
			SDP_UINT16, &hid_attr2[0] );
	sdp_attr_add_new ( &record, SDP_ATTR_HID_BOOT_DEVICE,
			SDP_UINT16, &hid_attr2[1] );
	// Submit our IDEA of a SDP record to the "sdpd"
        if (sdp_record_register(session, &record, SDP_RECORD_PERSIST) < 0) {
                fprintf ( stderr, "Service Record registration failed\n" );
                return -1;
        }
	// Store the service handle retrieved from there for reference (i.e.,
	// deleting the service info when this program terminates)
	sdphandle = record.handle;
        fprintf ( stdout, "HID keyboard/mouse service registered\n" );
        return 0;
}

/*
 * 	sdpunregister - Remove SDP entry for HID service on program termination
 * 	Parameters: SDP handle (typically 0x10004 or similar)
 */
void	sdpunregister ( uint32_t handle )
{
        uint32_t	range=0x0000ffff;
	sdp_list_t    *	attr;
	sdp_session_t *	sess;
	sdp_record_t  *	rec;
	// Connect to the local SDP server
	sess = sdp_connect(BDADDR_ANY, BDADDR_LOCAL, 0);
	if ( !sess )	return;
	attr = sdp_list_append(0, &range);
	rec = sdp_service_attr_req(sess, handle, SDP_ATTR_REQ_RANGE, attr);
	sdp_list_free(attr, 0);
	if ( !rec ) {
		sdp_close(sess);
		return;
	}
	sdp_device_record_unregister(sess, BDADDR_ANY, rec);
	sdp_close(sess);
	// We do not care wether unregister fails. If it does, we cannot help it.
	return;
}

static void add_lang_attr(sdp_record_t *r)
{
        sdp_lang_attr_t base_lang;
        sdp_list_t *langs = 0;
        /* UTF-8 MIBenum (http://www.iana.org/assignments/character-sets) */
        base_lang.code_ISO639 = (0x65 << 8) | 0x6e;
        base_lang.encoding = 106;
        base_lang.base_offset = SDP_PRIMARY_LANG_BASE;
        langs = sdp_list_append(0, &base_lang);
        sdp_set_lang_attr(r, langs);
        sdp_list_free(langs, 0);
}

// Wrapper for bind, caring for all the surrounding variables
int	btbind ( int sockfd, unsigned short port ) {
	struct sockaddr_l2 l2a;
	int i;
	memset ( &l2a, 0, sizeof(l2a) );
	l2a.l2_family = AF_BLUETOOTH;
	bacpy ( &l2a.l2_bdaddr, BDADDR_ANY );
	l2a.l2_psm = htobs ( port );
	i = bind ( sockfd, (struct sockaddr *)&l2a, sizeof(l2a) );
	if ( 0 > i )
	{
		fprintf ( stderr, "Bind error (PSM %d): %s\n",
				port, strerror ( errno ) );
	}
	return	i;
}


/*
 *	initfifo(filename) - creates (if necessary) and opens fifo
 *	instead of event devices. If filename exists and is NOT a fifo,
 *	abort with error.
 */
int	initfifo ( char *filename )
{
	struct stat ss;
	if ( NULL == filename ) return 0;
	if ( 0 == stat ( filename, &ss ) )
	{
		if ( ! S_ISFIFO(ss.st_mode) )
		{
			fprintf(stderr,"File [%s] exists, but is not a fifo.\n", filename );
			return 0;
		}
	} else {
		if ( 0 != mkfifo ( filename, S_IRUSR | S_IWUSR ) )
		{	// default permissions for created fifo is rw------- (user=rw)
			fprintf(stderr,"Failed to create new fifo [%s]\n", filename );
			return 0;
		}
	}
	eventdevs[0] = open ( filename, O_RDONLY | O_NONBLOCK );
	if ( 0 > eventdevs[0] )
	{
		fprintf ( stderr, "Failed to open fifo [%s] for reading.\n", filename );
		return 0;
	}
	return	1;
}

/*
 * 	initevents () - opens all required event files
 * 	or only one device, if number useonlyone is >= 0
 *	try to disable in X11 if mutex11 is set to 1
 * 	returns number of successfully opened event file nodes, or <1 for error
 */
int	initevents ( int useonlyone, int mutex11 )
{
	int	i, j, k;
	char	buf[sizeof(EVDEVNAME)+8];
	char	*xinlist = NULL;
	FILE	*pf;
	char	*p, *q;
	if ( mutex11 )
	{
		if ( NULL == ( xinlist = malloc ( 4096 ) ) )
		{
			printf ( "Memory alloc error\n" );
			return 0;
		}
		bzero ( xinlist, 4096 );
		if ( NULL != ( pf = popen ("xinput --list --short", "r" ) ) )
		{
			if ( 1 > fread ( xinlist, 1, 3800, pf ) )
			{
				printf ( "\tx11-mutable information not available.\n" );
				free ( xinlist );
				xinlist = NULL;
			}
		}
		fclose ( pf );
	}
	for ( i = 0; i < MAXEVDEVS; ++i )
	{
		eventdevs[i] = -1;
		x11handles[i] = -1;
	}
	for ( i = j = 0; j < MAXEVDEVS; ++j )
	{
		if ( ( useonlyone >= 0 ) && ( useonlyone != j ) ) { continue; }
		sprintf ( buf, EVDEVNAME, j );
		eventdevs[i] = open ( buf, O_RDONLY );
		if ( 0 <= eventdevs[i] )
		{
			fprintf ( stdout, "Opened %s as event device [counter %d]\n", buf, i );
			if ( ( mutex11 > 0 ) && ( xinlist != NULL ) )
			{
				k = -1;
				xinlist[3801] = 0;
				if ( ioctl(eventdevs[i], EVIOCGNAME(256),xinlist+3801) >= 0 )
				{
					p = xinlist;
					xinlist[4056] = 0;
					if ( strlen(xinlist+3801) < 4 ) // min lenght for name
						p = xinlist + 4056;
					while ( (*p != 0) &&
						( NULL != ( p = strstr ( p, xinlist+3801 ) ) ) )
					{
						q = p + strlen(xinlist+3801);
						while ( *q == ' ' ) ++q;
						if ( strncmp ( q, "\tid=", 4 ) == 0 )
						{
							k = atoi ( q + 4 );
							p = xinlist + 4056;
						} else {
							p = q;
						}
					}
				}
				if ( k >= 0 ) {
					//sprintf ( xinlist+3801, "xinput set-int-prop %d \"Device Enabled\" 8 0", k );
                    id = k;
					//if ( system ( xinlist + 3801 ) )
					//{
					//	fprintf ( stderr, "Failed to x11-mute.\n" );
					//}
					//x11handles[i] = k;
				}
			}
			++i;
		}
	}
	if ( xinlist != NULL ) { free ( xinlist ); }
	return	i;
}

void	closeevents ( void )
{
	int	i;
	char	buf[256];
	for ( i = 0; i < MAXEVDEVS; ++i )
	{
		if ( eventdevs[i] >= 0 )
		{
			close ( eventdevs[i] );
			if ( x11handles[i] >= 0 )
			{
				sprintf ( buf, "xinput set-int-prop %d \"Device "\
				"Enabled\" 8 1", x11handles[i] );
				if ( system ( buf ) )
				{
					fprintf ( stderr, "Failed to x11-unmute device %d.\n", i );
				}
			}
		}
	}
	return;
}

void	closefifo ( void )
{
	if ( eventdevs[0] >= 0 )
		close(eventdevs[0]);
	return;
}

void	cleanup_stdin ( void )
{
	// Cleans everything but the characters after the last ENTER keypress.
	// This is necessary BECAUSE while reading all keyboard input from the
	// event devices, those key presses will still stay in the stdin queue.
	// We do not want to have a backlog of hundreds of characters, possibly
	// commands and so on.
	fd_set fds;
	struct timeval tv;
	FD_ZERO ( &fds );
	FD_SET ( 0, &fds );
	tv.tv_sec  = 0;
	tv.tv_usec = 0;
	char buf[8];
	while ( 0 < select ( 1, &fds, NULL, NULL, &tv ) )
	{
		while ( read ( 0, buf, 8 ) ) {;}
		FD_ZERO ( &fds );
		FD_SET ( 0, &fds );
		tv.tv_sec  = 0;
		tv.tv_usec = 1;
	}
	close ( 0 );
	return;
}

int	add_filedescriptors ( fd_set * fdsp )
{
	// Simply add all open eventdev fds to the fd_set for select.
	int	i, j;
	FD_ZERO ( fdsp );
	j = -1;
	for ( i = 0; i < MAXEVDEVS; ++i )
	{
		if ( eventdevs[i] >= 0 )
		{
			FD_SET ( eventdevs[i], fdsp );
			if ( eventdevs[i] > j )
			{
				j = eventdevs[i];
			}
		}
	}
	return	j;
}

/*
 *	list_input_devices - Show a human-readable list of all input devices
 *	the current user has permissions to read from.
 *	Add info wether this probably can be "muted" in X11 if requested
 */
int	list_input_devices ()
{
	int	i, fd;
	char	buf[sizeof(EVDEVNAME)+8];
	struct input_id device_info;
	char	namebuf[256];
	char	*xinlist;
	FILE	*pf;
	char	*p, *q;
	char	x11 = 0;
	if ( NULL == ( xinlist = malloc ( 4096 ) ) )
	{
		printf ( "Memory alloc error\n" );
		return	1;
	}
	bzero ( xinlist, 4096 );
	if ( NULL != ( pf = popen ("xinput --list --name-only", "r" ) ) )
	{
		if ( 1 > fread ( xinlist, 1, 4095, pf ) )
		{
			printf ( "\tx11-mutable information not available.\n" );
		}
		fclose ( pf );
	}
	printf ( "List of available input devices:\n");
	printf ( "num\tVendor/Product, Name, -x compatible (x/-)\n" );
	for ( i = 0; i < MAXEVDEVS; ++i )
	{
		sprintf ( buf, EVDEVNAME, i );
		fd = open ( buf, O_RDONLY );
		if ( fd < 0 )
		{
			if ( errno == ENOENT ) { i = MAXEVDEVS ; break; }
			if ( errno == EACCES )
			{
				printf ( "%2d:\t[permission denied]\n", i );
			}
			continue;
		}
		if ( ioctl ( fd, EVIOCGID, &device_info ) < 0 )
		{
			close(fd); continue;
		}
		if ( ioctl ( fd, EVIOCGNAME(sizeof(namebuf)-4), namebuf+2) < 0 )
		{
			close(fd); continue;
		}
		namebuf[sizeof(namebuf)-4] = 0;
		x11 = 0;
		p = xinlist;
		while ( ( p != NULL ) && ( *p != 0 ) )
		{
			if ( NULL == ( q = strchr ( p, 0x0a ) ) ) { break; }
			*q = 0;
			if ( strcmp ( p, namebuf + 2 ) == 0 ) { x11 = 1; }
			*q = 0x0a;
			while ( (*q > 0) && (*q <= 0x20 ) ) { ++q; }
			p = q;
		}
		printf("%2d\t[%04hx:%04hx.%04hx] '%s' (%s)", i,
			device_info.vendor, device_info.product,
			device_info.version, namebuf + 2, x11 ? "+" : "-");
		printf("\n");
		close ( fd );
	}
	free ( xinlist );
	return	0;
}

/*	parse_events - At least one filedescriptor can now be read
 *	So retrieve data and parse it, eventually sending out a hid report!
 *	Return value <0 means connection broke and shall be disconnected
 */
int	parse_events ( fd_set * efds, int sockdesc )
{
	int	i, j;
	signed char	c;
	unsigned char	u;

    unsigned char layer = 0;
    unsigned char mod = 0;
    unsigned char printchar = 0;
    unsigned short  pressedmod = 0;
    unsigned char layermod = 0;

	char	buf[sizeof(struct input_event)];
	char	hidrep[32]; // mouse ~6, keyboard ~11 chars
	struct input_event    * inevent = (void *)buf;
	struct hidrep_mouse_t * evmouse = (void *)hidrep;
	struct hidrep_keyb_t  * evkeyb  = (void *)hidrep;
	if ( efds == NULL ) { return -1; }
	for ( i = 0; i < MAXEVDEVS; ++i )
	{
		if ( 0 > eventdevs[i] ) continue;
		if ( ! ( FD_ISSET ( eventdevs[i], efds ) ) ) continue;
		j = read ( eventdevs[i], buf, sizeof(struct input_event) );
		if ( j == 0 )
		{
			if ( debugevents & 0x1 ) fprintf(stderr,".");
			continue;
		}
		if ( -1 == j )
		{
			if ( debugevents & 0x1 )
			{
				if ( errno > 0 )
				{
					fprintf(stderr,"%d|%d(%s) (expected %d bytes). ",eventdevs[i],errno,strerror(errno), (int)sizeof(struct input_event));
				}
				else
				{
					fprintf(stderr,"j=-1,errno<=0...");
				}
			}
			continue;
		}
		if ( sizeof(struct input_event) > j )
		{
			// exactly 24 on 64bit, (16 on 32bit): sizeof(struct input_event)
			//  chars expected != got: data invalid, drop it!
			continue;
		}
		//fprintf(stderr,"   read(%d)from(%d)   ", j, i );
		if ( debugevents & 0x1 )
			fprintf ( stdout, "EVENT{%04X %04X %08X}\n", inevent->type,
			  inevent->code, inevent->value );
		switch ( inevent->type )
		{
		  case	EV_SYN:
			break;
		  case	EV_KEY:
			u = 1; // Modifier keys

            mod = 0;
            layer = 0;
            pressedmod = 0;
            layermod = 0;

			switch ( inevent->code )
			{
			  // *** Mouse button events
			  case	BTN_LEFT:
			  case	BTN_RIGHT:
			  case	BTN_MIDDLE:
				c = 1 << (inevent->code & 0x03);
				mousebuttons = mousebuttons & (0x07-c);
				if ( inevent->value == 1 )
				// Key has been pressed DOWN
				{
					mousebuttons=mousebuttons | c;
				}
				evmouse->btcode = 0xA1;
				evmouse->rep_id = REPORTID_MOUSE;
				evmouse->button = mousebuttons & 0x07;
				evmouse->axis_x =
				evmouse->axis_y =
				evmouse->axis_z = 0;
				if ( ! connectionok )
					break;
				j = send ( sockdesc, evmouse,
					sizeof(struct hidrep_mouse_t),
					MSG_NOSIGNAL );
				if ( 1 > j )
				{
					return	-1;
				}
				break;
			  // *** Special key: PRINT
			  case	KEY_SYSRQ:	
				// When pressed: abort connection
				if ( inevent->value == 0 )
				{

				    // If also LCtrl pressed:
				    // Terminate program
				    if (( modifierkeys & 0x1 ) == 0x1 )
				    {
                      if ( connectionok )
				      {
					    evkeyb->btcode=0xA1;
					    evkeyb->rep_id=REPORTID_KEYBD;
                        memset ( evkeyb->key, 0, 8 );
				        evkeyb->modify = 0;
					    j = send ( sockdesc, evkeyb,
					    sizeof(struct hidrep_keyb_t),
					    MSG_NOSIGNAL );
				      }
                      sprintf ( result, "xinput set-int-prop %d \"Device "\
					  "Enabled\" 8 1", id);
					  if ( system ( result ) )
					  {
					    fprintf ( stderr, "Failed to x11-mute or x11-unmute.\n" );
					  }
					  exit(0);//return	-99;
				    }

                    //if RCtrl pressed:
                    //send defined password to device
                    if (( modifierkeys & 0x10 ) == 0x10 )
				    {
                      int i;
                      for(i=0;i<ARRAY;i++) {

                       mod = pass[i][0];
                       pressedkey[0] = pass[i][1];

                       evkeyb->btcode = 0xA1;
				       evkeyb->rep_id = REPORTID_KEYBD;
                       memcpy ( evkeyb->key, pressedkey, 8 );
				       evkeyb->modify = mod;
                       //printf("\nsend mod: 0x%08x, pressedkey: %u,%u,%u,%u,%u,%u,%u,%u",mod,pressedkey[0],pressedkey[1],pressedkey[2],pressedkey[3],pressedkey[4],pressedkey[5],pressedkey[6],pressedkey[7]);
				       if ( ! connectionok ) break;
                         if (on) {
				           j = send ( sockdesc, evkeyb,
					       sizeof(struct hidrep_keyb_t),
					       MSG_NOSIGNAL );
                         }
				         if ( 1 > j )
				         {
					       // If sending data fails,
					       // abort connection
					       return	-1;
				         }
                      }
                      pressedkey[0]=0;
					  break;
				    }

                    on = !on;
                    if (stop_writing) {
                      if (!id){
                        break;
                      }
				    	sprintf ( result, "xinput set-int-prop %d \"Device "\
				    		"Enabled\" 8 %u", id , !on);
				    	if ( system ( result ) )
				    	{
				        	fprintf ( stderr, "Failed to x11-mute or x11-unmute.\n" );
					  }
                    }
				}
				break;


			  // *** "Modifier" key events
			  case	KEY_RIGHTMETA:
				pressedmod = 0x8080;
                break;
			  case	KEY_RIGHTCTRL:
				pressedmod = 0x8010;
                break;
			  case	KEY_LEFTMETA:
				pressedmod = 0x8008;
                break;
			  case	KEY_LEFTALT:
				pressedmod = 0x8004;
                break;
			  case	KEY_LEFTCTRL:
                pressedmod = 0X8001;
                break;
			  case	KEY_LEFTSHIFT: //2 
                pressedmod = 0x0002;
                break;
     		  case	KEY_RIGHTALT: //64
				pressedmod = 0x0040;
                break;
			  case	KEY_RIGHTSHIFT: //32
				pressedmod = 0x0020;
                break;
              case	KEY_CAPSLOCK:
                pressedmod = 0x0100; //57 
                break;
              case	KEY_BACKSLASH:
                pressedmod = 0x0200; //49 #
                break;
              case	KEY_102ND:
                pressedmod = 0x0400; //50 <
                break;

// *** Regular key events
			  case	KEY_KPDOT:	++u; // Keypad Dot ~ 99
			  case	KEY_KP0:	++u; // code 98...
			  case	KEY_KP9:	++u; // countdown...
			  case	KEY_KP8:	++u;
			  case	KEY_KP7:	++u;
			  case	KEY_KP6:	++u;
			  case	KEY_KP5:	++u;
			  case	KEY_KP4:	++u;
			  case	KEY_KP3:	++u;
			  case	KEY_KP2:	++u;
			  case	KEY_KP1:	++u;
			  case	KEY_KPENTER:	++u;
			  case	KEY_KPPLUS:	++u;
			  case	KEY_KPMINUS:	++u;
			  case	KEY_KPASTERISK:	++u;
			  case	KEY_KPSLASH:	++u;
			  case	KEY_NUMLOCK:	++u;
			  case	KEY_UP:		++u;
			  case	KEY_DOWN:	++u;
			  case	KEY_LEFT:	++u;
			  case	KEY_RIGHT:	++u;
			  case	KEY_PAGEDOWN:	++u;
			  case	KEY_END:	++u;
			  case	KEY_DELETE:	++u;
			  case	KEY_PAGEUP:	++u;
			  case	KEY_HOME:	++u;
			  case	KEY_INSERT:	++u;
			  case  KEY_PAUSE:  ++u; //[Pause] key
			  case	KEY_SCROLLLOCK:	++u;
			  ++u; //[printscr] SYSRQ
			  case	KEY_F12:	++u; //F12=> code 69
			  case	KEY_F11:	++u;
			  case	KEY_F10:	++u;
			  case	KEY_F9:		++u;
			  case	KEY_F8:		++u;
			  case	KEY_F7:		++u;
			  case	KEY_F6:		++u;
			  case	KEY_F5:		++u;
			  case	KEY_F4:		++u;
			  case	KEY_F3:		++u;
			  case	KEY_F2:		++u;
			  case	KEY_F1:		++u;
			  ++u; // CAPSLOCK
			  case	KEY_SLASH:	++u;
			  case	KEY_DOT:	++u;
			  case	KEY_COMMA:	++u;
			  case	KEY_GRAVE:	++u;
			  case	KEY_APOSTROPHE:	++u;
			  case	KEY_SEMICOLON:	++u;
			  ++u; //102ND
			  ++u; //BACKSLASH
			  case	KEY_RIGHTBRACE:	++u;
			  case	KEY_LEFTBRACE:	++u;
			  case	KEY_EQUAL:	++u;
			  case	KEY_MINUS:	++u;
			  case	KEY_SPACE:	++u;
			  case	KEY_TAB:	++u;
			  case	KEY_BACKSPACE:	++u;
			  case	KEY_ESC:	++u;
			  case	KEY_ENTER:	++u; //Return=> code 40
			  case	KEY_0:		++u;
			  case	KEY_9:		++u;
			  case	KEY_8:		++u;
			  case	KEY_7:		++u;
			  case	KEY_6:		++u;
			  case	KEY_5:		++u;
			  case	KEY_4:		++u;
			  case	KEY_3:		++u;
			  case	KEY_2:		++u;
			  case	KEY_1:		++u;
			  case	KEY_Z:		++u;
			  case	KEY_Y:		++u;
			  case	KEY_X:		++u;
			  case	KEY_W:		++u;
			  case	KEY_V:		++u;
			  case	KEY_U:		++u;
			  case	KEY_T:		++u;
			  case	KEY_S:		++u;
			  case	KEY_R:		++u;
			  case	KEY_Q:		++u;
			  case	KEY_P:		++u;
			  case	KEY_O:		++u;
			  case	KEY_N:		++u;
			  case	KEY_M:		++u;
			  case	KEY_L:		++u;
			  case	KEY_K:		++u;
			  case	KEY_J:		++u;
			  case	KEY_I:		++u;
			  case	KEY_H:		++u;
			  case	KEY_G:		++u;
			  case	KEY_F:		++u;
			  case	KEY_E:		++u;
			  case	KEY_D:		++u;
			  case	KEY_C:		++u;
			  case	KEY_B:		++u;
			  case	KEY_A:		u +=3;	// A =>  4

			  default:
				// Unknown key usage - ignore that
			  ;
            }

                modifierkeys &= ( 0xffff - pressedmod ); //delete modifier
				if ( inevent->value >= 1 ) //if value = 1 add it again
				{
					modifierkeys |= pressedmod; //add modifier
				}

                //if pressedmod is not an neo-modifier
                if (pressedmod & 0x8000) {
                  mod = (char) modifierkeys;
                }

              
                //Decide neo-layer by pressed modifiers
                if(modifierkeys & 0x0022) {
                  layermod |= 0x01;
                }
                if(modifierkeys & 0x0300) {
                  layermod |= 0x02;
                }
                if(modifierkeys & 0x0440) {
                  layermod |= 0x04;
                }

                if((layermod & 0x01) == 0x01) {
                  layer = 1;
                }
                if((layermod & 0x02) == 0x02) {
                  layer = 2;
                }
                if((layermod & 0x04) == 0x04) {
                  layer = 3;
                }
                if((layermod & 0x03) == 0x03) {
                  layer = 4;
                }
                if((layermod & 0x06) == 0x06) {
                  layer = 5;
                }


                //get char for the pressed character and layer
                printchar = chars[u][layer][1];

                if(printchar) {
                  //get mod for the pressed charcter and layer
                  mod = chars[u][layer][0];
                  layer = 0;
                }
				
				if ( inevent->value == 1 )
				{
					// "Key down": Add to list of
					// currently pressed keys
					for ( j = 0; j < 8; ++j )
					{
					    if (pressedkey[j] == 0)
					    {
						pressedkey[j]=printchar;
						j = 8;
					    }
					    else if(pressedkey[j] == printchar)
					    {
						j = 8;
					    }
					}
				}
				else if ( inevent->value == 0 )
				{	// KEY UP: Remove from array
					for ( j = 0; j < 8; ++j )
					{
					    if ( pressedkey[j] == printchar )
					    {
						while ( j < 7 )
						{
						    pressedkey[j] =
							pressedkey[j+1];
						    ++j;
						}
					    pressedkey[7] = 0;
					    }
					}
				} 
				else	// "Key repeat" event
				{
					; // This should be handled
					// by the remote side, not us.
				}


                evkeyb->btcode = 0xA1;
				evkeyb->rep_id = REPORTID_KEYBD;
				memcpy ( evkeyb->key, pressedkey, 8 );
				evkeyb->modify = mod;
                //printf("\nsend mod: 0x%08x, pressedkey: %u,%u,%u,%u,%u,%u,%u,%u",mod,pressedkey[0],pressedkey[1],pressedkey[2],pressedkey[3],pressedkey[4],pressedkey[5],pressedkey[6],pressedkey[7]);
				if ( ! connectionok ) break;
                if (on) {
				j = send ( sockdesc, evkeyb,
					sizeof(struct hidrep_keyb_t),
					MSG_NOSIGNAL );
                }
				if ( 1 > j )
				{
					// If sending data fails,
					// abort connection
					return	-1;
				}

			break;
		  // *** Mouse movement events
		  case	EV_REL:
			switch ( inevent->code )
			{
			  case	ABS_X:
			  case	ABS_Y:
			  case	ABS_Z:
			  case	REL_WHEEL:
				evmouse->btcode = 0xA1;
				evmouse->rep_id = REPORTID_MOUSE;
				evmouse->button = mousebuttons & 0x07;
				evmouse->axis_x =
					( inevent->code == ABS_X ?
					  inevent->value : 0 );
				evmouse->axis_y =
					( inevent->code == ABS_Y ?
					  inevent->value : 0 );
				evmouse->axis_z =
					( inevent->code >= ABS_Z ?
					  inevent->value : 0 );
				if ( ! connectionok ) break;
				j = send ( sockdesc, evmouse,
					sizeof(struct hidrep_mouse_t),
					MSG_NOSIGNAL );
				if ( 1 > j )
				{
					return	-1;
				}
				break;
			}
			break;
		  // *** Various events we do not know. Ignore those.
		  case	EV_ABS:
		  case	EV_MSC:
		  case	EV_LED:
		  case	EV_SND:
		  case	EV_REP:
		  case	EV_FF:
		  case	EV_PWR:
		  case	EV_FF_STATUS:
			break;
		}

	}
	return	0;
}

int	main ( int argc, char ** argv )
{
	int			i,  j;
	int			sockint, sockctl; // For the listening sockets
	struct sockaddr_l2	l2a;
	socklen_t		alen=sizeof(l2a);
	int			sint,  sctl;	  // For the one-session-only
						  // socket descriptor handles
	char			badr[40];
	fd_set			fds;		  // fds for listening sockets
	fd_set			efds;	          // dev-event file descriptors
	int			maxevdevfileno;
	char			skipsdp = 0;	  // On request, disable SDPreg
	struct timeval		tv;		  // Used for "select"
	int			onlyoneevdev = -1;// If restricted to using only one evdev
	int			mutex11 = 0;      // try to "mute" in x11?
	char			*fifoname = NULL; // Filename for fifo, if applicable
	// Parse command line
	for ( i = 1; i < argc; ++i )
	{
		if ( ( 0 == strcmp ( argv[i], "-h"     ) ) ||
		     ( 0 == strcmp ( argv[i], "-?"     ) ) ||
		     ( 0 == strcmp ( argv[i], "--help" ) ) )
		{
			showhelp();
			return	0;
		}
		else if ( ( 0 == strcmp ( argv[i], "-s" ) ) ||
			  ( 0 == strcmp ( argv[i], "--skipsdp" ) ) )
		{
			skipsdp = 1;
		}
		else if ( 0 == strncmp ( argv[i], "-e", 2 ) ) {
			onlyoneevdev = atoi(argv[i]+2);
		}
		else if ( 0 == strcmp ( argv[i], "-l" ) )
		{
			return list_input_devices();
		}
		else if ( 0 == strcmp ( argv[i], "-d" ) )
		{
			debugevents = 0xffff;
		}
		else if ( 0 == strcmp ( argv[i], "-x" ) )
		{
			mutex11 = 1;
            stop_writing = 1;

            if ( NULL == ( result = malloc ( 512 ) ) )
		    {
			   printf ( "Memory alloc error\n" );
			   return 1;
		    }

		}
		else if ( 0 == strncmp ( argv[i], "-f", 2 ) )
		{
			fifoname = argv[i] + 2;
		}
		else
		{
			fprintf ( stderr, "Invalid argument: \'%s\'\n", argv[i]);
			return	1;
		}
	}
	if ( ! skipsdp )
	{
		if ( dosdpregistration() )
		{
			fprintf(stderr,"Failed to register with SDP server\n");
			return	1;
		}
	}
	if ( NULL == fifoname )
	{
		if ( 1 > initevents (onlyoneevdev, mutex11) )
		{
			fprintf ( stderr, "Failed to open event interface files\n" );
			return	2;
		}
	} else {
		if ( 1 > initfifo ( fifoname ) )
		{
			fprintf ( stderr, "Failed to create/open fifo [%s]\n", fifoname );
			return	2;
		}
	}
	maxevdevfileno = add_filedescriptors ( &efds );
	if ( maxevdevfileno <= 0 )
	{
		fprintf ( stderr, "Failed to organize event input.\n" );
		return	13;
	}
	sockint = socket ( AF_BLUETOOTH, SOCK_SEQPACKET, BTPROTO_L2CAP );
	sockctl = socket ( AF_BLUETOOTH, SOCK_SEQPACKET, BTPROTO_L2CAP );
	if ( ( 0 > sockint ) || ( 0 > sockctl ) )
	{
		fprintf ( stderr, "Failed to generate bluetooth sockets\n" );
		return	2;
	}
	if ( btbind ( sockint, PSMHIDINT ) || btbind ( sockctl, PSMHIDCTL ))
	{
		fprintf ( stderr, "Failed to bind sockets (%d/%d) "
				"to PSM (%d/%d)\n",
				sockctl, sockint, PSMHIDCTL, PSMHIDINT );
		return	3;
	}
	if ( listen ( sockint, 1 ) || listen ( sockctl, 1 ) )
	{
		fprintf ( stderr, "Failed to listen on int/ctl BT socket\n" );
		close ( sockint );
		close ( sockctl );
		return	4;
	}
	// Add handlers to catch signals:
	// All do the same, terminate the program safely
	// Ctrl+C will be ignored though (SIGINT) while a connection is active
	signal ( SIGHUP,  &onsignal );
	signal ( SIGTERM, &onsignal );
	signal ( SIGINT,  &onsignal );
	fprintf ( stdout, "The HID-Client is now ready to accept connections "
			"from another machine\n" );
	//i = system ( "stty -echo" );	// Disable key echo to the console
	while ( 0 == prepareshutdown )
	{	// Wait for any shutdown-event to occur
		sint = sctl = 0;
		add_filedescriptors ( &efds );
		tv.tv_sec  = 0;
		tv.tv_usec = 0;
		while ( 0 < (j = select(maxevdevfileno+1,&efds,NULL,NULL,&tv)))
		{	// Collect and discard input data as long as available
			if ( -1 >  ( j = parse_events ( &efds, 0 ) ) )
			{	// LCtrl-LAlt-PAUSE - terminate program
				prepareshutdown = 1;
				break;
			}
			add_filedescriptors ( &efds );
			tv.tv_sec  = 0;
			tv.tv_usec = 500; // minimal delay
		}
		if ( prepareshutdown )
			break;
		connectionok = 0;
		tv.tv_sec  = 1;
		tv.tv_usec = 0;
		FD_ZERO ( &fds );
		FD_SET  ( sockctl, &fds );
		j = select ( sockctl + 1, &fds, NULL, NULL, &tv );
		if ( j < 0 )
		{
			if ( errno == EINTR )
			{	// Ctrl+C ? - handle that elsewhere
				continue;
			}
			fprintf ( stderr, "select() error on BT socket: %s! "
					"Aborting.\n", strerror ( errno ) );
			return	11;
		}
		if ( j == 0 )
		{	// Nothing happened, check for shutdown req and retry
			if ( debugevents & 0x2 )
				fprintf ( stdout, "," );
			continue;
		}
		sctl = accept ( sockctl, (struct sockaddr *)&l2a, &alen );
		if ( sctl < 0 )
		{
			if ( errno == EAGAIN )
			{
				continue;
			}
			fprintf ( stderr, "Failed to get a control connection:"
					" %s\n", strerror ( errno ) );
			continue;
		}
		tv.tv_sec  = 3;
		tv.tv_usec = 0;
		FD_ZERO ( &fds );
		FD_SET  ( sockint, &fds );
		j = select ( sockint + 1, &fds, NULL, NULL, &tv );
		if ( j < 0 )
		{
			if ( errno == EINTR )
			{	// Might have been Ctrl+C
				close ( sctl );
				continue;
			}
			fprintf ( stderr, "select() error on BT socket: %s! "
					"Aborting.\n", strerror ( errno ) );
			return	12;
		}
		if ( j == 0 )
		{
			fprintf ( stderr, "Interrupt connection failed to "
					"establish (control connection already"
					" there), timeout!\n" );
			close ( sctl );
			continue;
		}
		sint = accept ( sockint, (struct sockaddr *)&l2a, &alen );
		if ( sint < 0 )
		{
			close ( sctl );
			if ( errno == EAGAIN )
				continue;
			fprintf ( stderr, "Failed to get an interrupt "
					"connection: %s\n", strerror(errno));
			continue;
		}
		ba2str ( &l2a.l2_bdaddr, badr );
		badr[39] = 0;
		fprintf ( stdout, "Incoming connection from node [%s] "
				"accepted and established.\n", badr );
		tv.tv_sec  = 0;
		tv.tv_usec = 0;
		j = -1;
		add_filedescriptors ( &efds );
		while ( 0 < (j = select(maxevdevfileno+1,&efds,NULL,NULL,&tv)))
		{
			// This loop removes all input garbage that might be
			// already in the queue
			if ( -1 > ( j = parse_events ( &efds, 0 ) ) )
			{	// LCtrl-LAlt-PAUSE - terminate program
				prepareshutdown = 1;
				break;
			}
			add_filedescriptors ( &efds );
			tv.tv_sec  = 0;
			tv.tv_usec = 0;
		}
		if ( prepareshutdown )
			break;
		connectionok = 1;
		memset ( pressedkey, 0, 8 );
		modifierkeys = 0;
		mousebuttons = 0;
		while ( connectionok )
		{
			add_filedescriptors ( &efds );
			tv.tv_sec  = 1;
			tv.tv_usec = 0;
			while ( 0 < ( j = select ( maxevdevfileno + 1, &efds,
							NULL, NULL, &tv ) ) )
			{
				if ( 0 > ( j = parse_events ( &efds, sint ) ) )
				{
					// PAUSE pressed - close connection
					connectionok = 0;
					if ( j < -1 )
					{	// LCtrl-LAlt-PAUSE - terminate
						close ( sint );
						close ( sctl );
						prepareshutdown = 1;
					}
					break;
				}
				add_filedescriptors ( &efds );
				tv.tv_sec  = 1;
				tv.tv_usec = 0;
			}
		}
		connectionok = 0;
		close ( sint );
		close ( sctl );
		sint = sctl =  0;
		fprintf ( stderr, "Connection closed\n" );
		usleep ( 500000 ); // Sleep 0.5 secs between connections
				   // to not be flooded
	}
	//i = system ( "stty echo" );	   // Set console back to normal
	close ( sockint );
	close ( sockctl );
	if ( ! skipsdp )
	{
		sdpunregister ( sdphandle ); // Remove HID info from SDP server
	}
	if ( NULL == fifoname )
	{
		closeevents ();
	} else {
		closefifo ();
	}
	cleanup_stdin ();	   // And remove the input queue from stdin
	fprintf ( stderr, "Stopped hidclient.\n" );
	return	0;
}


void	showhelp ( void )
{
	fprintf ( stdout,
"hidclient  -  Virtual Bluetooth Mouse and Keyboard\n\n" \
"hidclient allows you to emulate a bluetooth HID device, based on the\n" \
"Bluez Bluetooth stack for Linux.\n\n" \
"The following command-line parameters can be used:\n" \
"-h|-?		Show this information\n" \
"-e<num>\t	Use only the one event device numbered <num>\n" \
"-f<name>	Use fifo <name> instead of event input devices\n" \
"-l		List available input devices\n" \
"-x		Disable device in X11 while hidclient is running\n" \
"-s|--skipsdp	Skip SDP registration\n" \
"		Do not register with the Service Discovery Infrastructure\n" \
"		(for debug purposes)\n\n" \
"Using hidclient in conjunction with \'openvt\' is recommended to minize\n" \
"impact of keystrokes meant to be transmitted to the local user interface\n" \
"(like running hidclient from a xterm window). You can make \'openvt\'\n" \
"spawn a text mode console, switch there and run hidclient with the\n" \
"following command line:\n" \
"		openvt -s -w hidclient\n" \
"This will even return to your xsession after hidclient terminates.\n\n" \
"hidclient connections can be dropped at any time by pressing the PAUSE\n" \
"key; the program will wait for other connections afterward.\n" \
"To stop hidclient, press LeftCtrl+LeftAlt+Pause.\n"
		);
	return;
}

void	onsignal ( int i )
{
	// Shutdown should be done if:
	switch ( i )
	{
	  case	SIGINT:
		if ( 0 == connectionok )
		{
			// No connection is active and Ctrl+C is pressed
			prepareshutdown = 2;
		}
		else
		{	// Ctrl+C ignored while connected
			// because it might be meant for the remote
			return;
		}
	  case	SIGTERM:
	  case	SIGHUP:
		// If a signal comes in
		prepareshutdown = 1;
		fprintf ( stderr, "Got shutdown request\n" );
		break;
	}
	return;
}

