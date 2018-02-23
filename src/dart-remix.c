#if 0
  NAME="dart-remix"
  SRC="/data/DARTremix."
  echo -n self_compiling $SRC/$NAME
  echo '  CopyrightⒸ2016-2016.Bruce_Guenther_Baumgart.Software_License:GPL-v3.'
  gcc -g -m64 -Wall -Werror -o /usr/local/bin/$NAME $SRC/$NAME.c $SRC/md5.c
  return
#endif

typedef unsigned long long uint64;
typedef          long long  int64;
typedef unsigned long long u64;
typedef          long long i64;
typedef unsigned char uchar;

/* Read the 229 concatenated DART tapes from the 85GB file named "/large/flat/dart/data8"

 * ------------------------------------------------------------------------------------ *
 *       D       A       R       T       -       R       E       M      I       X       *
 * ------------------------------------------------------------------------------------ *
 echo -n 'copyrightⒸ2016-2017 Bruce_Guenther_Baumgart software_license:GPL-v3.'

 Read the flat DART tape file from it default pathname /large/flat/dart/data8 which
 contains a concatenated image of all the reels of DART tape
 in a format called "data8" for "8 bytes per PDP10 word"
 where the 36-bit PDP10 words are right justified in 64-bits.

 de-frag         concated record data payload into blobs
 de-dup          hash digest to serial number unique blob content
 de-damage       Mark files with Previous-Media-Error or defective headings,
 de-flate        omit excessive record padding and redundancy
        then
 de-tox          omit ephemera

 This remix "knows" in advance that the record statistics are
 case  6: //     5,486. tape reel BOT and EOT markers HEAD and TAIL records
 case -3: // 1,886,472. file start records
 case  0: // 1,045,270. file continue records
 case -9: //        63. gap records
 and that the maximum record size is
 and that the maximum file blob size is
 the 1990 MCOPY *ERROR.ERR records number 
 the 1998 gaps number 61.

 Farb=0 indicates the highest level of authencity with a bit-exact equivalence to
 (and provenance from) the data read on the 229 reels of DART tape in 1998.

 Remix generates farb=1 files for 
 the BOT and EOT tape type=6 records, 
 the ERROR.ERR[ERR,OR␣] records, and for
 the -9,,Gap records.
 * ------------------------------------------------------------------------------------ *
USAGE:

Verify input tape is a bitwise exact copy of the original template
        time md5sum /large/flat/dart/data8
        3adbff17fd7f9f6eb9107755594ae0b9  /large/flat/dart/data8
        about 14 minutes

Initialize path names into a large disk area, for example mount fresh disk at /d
        mkdir /d/large
        # ROOT logical path /large/ points to actual container
        ln -s /d/large /large
        mkdir -p /large/{csv,log}
        mkdir -p /large/{data8,text,octal}/sn
        mkdir -p /large/flat/{dart,remix}

Clean off previous run
        find /large/{data8,text,log,octal,csv} -type f -exec rm '{}' \;
        find /large/flat/remix -type f -exec rm '{}' \;

Move off previous run
        cd /large
        mv log{,.$(date --i)};mkdir log
        mv csv{,.$(date --i)};mkdir csv

Self compile the dart-remix.x
*/
#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <search.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>
#include "md5.h"

FILE *metadata2;
//
//      This union defines PDP10 bit-field names
//      within one Big Endian 36-bit PDP10 word.
//
//      Programming Language 'C' x86 words are Little Endian,
//      so Right comes before Left.
typedef union {
  uint64 fw;
  struct {  int64  word:36,        :28; } full; //    signed
  struct {  int64 right:18,left:18,:28; } half; //    signed
  struct { uint64  word:36,        :28; } u36;  // Un-signed
  struct { uint64 right:18,left:18,:28; } u18;  // Un-signed
  struct { uint64 hi:12,mid:12,lo:12,:28; } third;
  struct { uint64 c6:6,c5:6,c4:6,c3:6,c2:6,c1:6,:28;}    sixbit; // sixbit+040
  struct { uint64 bit35:1,a5:7,a4:7,a3:7,a2:7,a1:7,:28;	} seven; // 'seven bit ASCII' or SAIL-ASCII
} pdp10_word;
//
// Doctored seven-bit SAIL-ASCII into UTF-8 string table.
//   ======================================================================
//    ↓αβ∧¬επλ\t\n\v\f\r∞∂⊂⊃∩∪∀∃⊗↔_→~≠≤≥≡∨ !\"#$%&'()*+,-./0123456789:;<=>?
//   @ABCDEFGH I J K L MNOPQRSTUVWXYZ[\\]↑←'abcdefghijklmnopqrstuvwxyz{|⎇}␈
//   ======================================================================
// without NUL, RETURN, ALT and RUBOUT !
//   codes \000 \015    \0175   \0177
//
char *SAIL_ASCII[]={
  // 00      01      02      03          04      05      06      07
  "",       "↓",    "α",    "β",         "∧",    "¬",    "ε",    "π",  //  000
  "λ",     "\t",   "\n",   "\v",        "\f",   "",      "∞",    "∂",  //  010
  "⊂",      "⊃",    "∩",    "∪",         "∀",    "∃",    "⊗",    "↔",  //  020
  "_",      "→",    "~",    "≠",         "≤",    "≥",    "≡",    "∨",  //  030
  " ",      "!",   "\"",    "#",         "$",    "%",    "&",    "'",  //  040
  "(",      ")",    "*",    "+",         ",",    "-",    ".",    "/",  //  050
  "0",      "1",    "2",    "3",         "4",    "5",    "6",    "7",  //  060
  "8",      "9",    ":",    ";",         "<",    "=",    ">",    "?",  //  070
  "@",      "A",    "B",    "C",         "D",    "E",    "F",    "G",  // 0100
  "H",      "I",    "J",    "K",         "L",    "M",    "N",    "O",  // 0110
  "P",      "Q",    "R",    "S",         "T",    "U",    "V",    "W",  // 0120
  "X",      "Y",    "Z",    "[",         "\\",   "]",    "↑",    "←",  // 0130
  "'",      "a",    "b",    "c",         "d",    "e",    "f",    "g",  // 0140
  "h",      "i",    "j",    "k",         "l",    "m",    "n",    "o",  // 0150
  "p",      "q",    "r",    "s",         "t",    "u",    "v",    "w",  // 0160
  "x",      "y",    "z",    "{",         "|",    "",     "}",    ""    // 0170
};
//
// Magnetic Tape defects seem to be mostly bit-drop outs,
// that is failures to detect magnetic one markings when reading the tape.
// So given two nearly identical files, the file with the highest bit count
// is more likely to be accurate. Initialization, at top of main:
// for(n=16;n<4095;n++){
// number_of_bits[n] = number_of_bits[n/256]+number_of_bits[(n/16)%16]+number_of_bits[n%16];
// number_of_bits[n] = number_of_bits[n>>8 ]+number_of_bits[(n>>4)&15]+number_of_bits[n&15];
// }
//                         0 1 2 3  4 5 6 7  8 9 A B  C D E F
int number_of_bits[4096]={ 0,1,1,2, 1,2,2,3, 1,2,2,3, 2,3,3,4, };
//
//      OUTPUT remix forks ( streams, data sets, tracks )
//              /large/flat/remix/
int o_fil;
int o_txt;
int o_bin;
int o_gap;
int o_err;
//
//      OUTPUT database tables
//      OUTPUT log text
//
FILE *snhash;
FILE *metadata;
FILE *rib;
FILE *air;
FILE *prm;
//
//      flat DART data8 tape buffer
//
// select a large buffer size, like 1 Gigabyte
#define DATASIZE 1024*1024*128
#define BILLION 1000000000LL
#define MILLION 1000000LL
#define HEAD 0125045414412LL
#define TAIL 0126441515412LL
pdp10_word buffer[DATASIZE];
//
//      Tape Record is a pointer into the buffer
//
pdp10_word *tape;
pdp10_word template[36]; // Copy from first 36. words of a -3 START_FILE tape record
//
// The remix record is a Tag-and-Blob representation for the WAITS-File-System.
//
typedef struct {
  uint64 record_length:32,     :32,
    zero_padding:32,           :32,
    
    prj:18,prg:18,              :28,
    filnam:36,                  :28,
    ext:18,typ:18,              :28,
    mdate:18,mtime:18,          :28,

    wrtppn:36,                  :28,
    wrtool:36,                  :28,
    
    sn:20,damage:6,             :38,
    drn:23,prot:9,mode:4,       :28;

  // farb:4
  // culor:32
} tag;
tag Tag;
//
//      Blob ( data portion of a file accumulated from
//              -3,,leng        File Start with all its
//               0,,leng        File Continued records.
//              -9,,0           gap record
//               leng           gap
//               6,,11.         BOT or EOT marker 12. words
//
//                      3020800 // words in largest blob
#define MAX_BYTE_COUNT 40000000 // Larger then any blob
#define MAX_WORD_COUNT ((MAX_BYTE_COUNT+4)/5)
pdp10_word blob[ MAX_WORD_COUNT ]; // 64-bit words.
char utf8[ MAX_BYTE_COUNT ];

int seen, blob_word_count, zcount;
//
//      DART tape file records (type -3 or 0) Headers, here DART-Header is named 'DARTH'.
//      In data8 format the sizeof(darth) is 280. bytes which contains 35. PDP10 words.
//
//      RIGHT halfword ,, LEFT halfword  ; 28. bits unused.
typedef struct {
  int64 leng:18,type:18,:28;            // word  0. Type,,Leng
  uint64 DSK___:36,:28;                 // word  1. 'DSK␣␣␣' marker
  // RIB = Retrieval-Information-Block for the SAIL Ralph File System
  uint64 filnam:36,:28;                 // word  2. FILNAM      DDNAM
  uint64 c_date:18,ext:18,:28;          // word  3. EXT         DDEXT
  uint64 date_lo:12,time:11,mode:4,prot:9,:28; // word  4.      DDPRO
  uint64 prg:18,prj:18,:28;             // word  5.             DDPPN
  uint64 track:36,:28;                  // word  6.             DDLOC
  uint64 count:22,:42;                  // word  7.             DDLNG           file size word count
  uint64 refdate:12, reftime:11, :41;   // word  8.             DREFTM          access date time
  uint64 dumpdate:15, dumptape:12, :2,  // word  9.             DDMPTM           dump  date time
    never:1, reap:1, P_invalid:1, P_count:3, TP:1;  // dart bookkeeping inside the disk file system
  uint64 word10:36,:28; // DGRP1R
  uint64 word11:36,:28; // DNXTGP
  uint64 word12:36,:28; // DSATID
  // DQINFO five words
  uint64 word13:36,:28;
  uint64 word14:36,:28;
  uint64 write_program:36,:28;  // word15. WPROGRM              WRTool
  uint64 write_ppn:36,:28;      // word16. WPPN                 WRTppn
  uint64 word17:36,:28;
  // Thin AIR: six words from master copy tape-to-tape, MCOPY Leader.
  uint64 DART__:36,:28; // word 18. 'DART  ' marker
  uint64 _FILE_:36,:28; // word 19. '*FILE*' or 'CON  #' marker
  uint64 word20:36,:28;
  uint64 word21:36,:28;
  uint64 word22:36,:28; // MCOPY class==2,,reel#3000 and up
  uint64 word23:36,:28;
  // Landmark AIR: five words of (sometimes unreliable / unnecessary) redundant information
  uint64 otnum:36,:28; // old tape number .. old or odd tape numbering 0 to 3526 seen
  uint64 word25:36,:28; //  0
  uint64 word26:36,:28; // -1
  uint64 word27:36,:28; //  0
  uint64 word28:36,:28; // words remaining
  // Clear AIR: seven word block of zeroes.
  uint64 word29:36,:28; // 0
  uint64 word30:36,:28; // 0
  uint64 word31:36,:28; // 0
  uint64 word32:36,:28; // 0
  uint64 word33:36,:28; // 0
  uint64 word34:36,:28; // 0
  uint64 word35:36,:28; // 0
} darth;
darth *V;
//
//      DART records 6,,000013 for BOT and EOT tape events
//
/* The HEADER AND TRAILER BLOCKS:
   Word  0: version,,length
   "version" is the positive version number of
   the DART that created this tape (VERSION);
   "length" is always octal 013, decimal 11.
   the length of the data following,
   including the rotated checksum word below.
   Word  1: 'DART  ' sixbit DART
   Word  2: '*HEAD*' or '*TAIL*'
   data in sixbit, indicates Header or Trailer block
   Word  3: time,date	in file system format
   Bits 13:23 are time in mins, bits 24:35 are date.
   Bits 4:12 are unused (considered high minutes).
   Version 5: Bits 0-2 are high date.
   Version 6: Bit 3 means this is time from prev media
   Word  4: ppn		the name of the person running Dart.
   Word  5: class,,tapno	Tape number of this tape
   Dump class of this dump
   The top bits of tapno indicate which
   sequence of tapes this nbr is in.
   Word  6: relative dump,,absolute dump	(relative is within this tape)
   Word  7: tape position in feet from load point
   Word  8:	 0		reserved for future use
   Word  9:	-1		all bits on
   Word 10:	 0		all bits off
   Word 11.	rotated checksum of words 1 through 12 above.
*/
typedef struct {
  int64 leng:18,type:18,:28;            // word#0.
  uint64 DART__:36,:28;                 // word#1.
  uint64 headtail:36,:28;               // word#2.
  uint64 date_lo:12,time:11+9,dateflag:1,date_hi:3,:28; // word#3
  uint64 prg:18,prj:18,:28;             // word#4. PPN
  uint64 tapeno:18,class:18,:28;        // word#5.
  uint64 word6:36,:28;                  // word#6.
  uint64 feet:36,:28;                   // word#7.
  uint64 zip8;                          // word#8 is always zero.
  int64 neg1:36,:28;                    // word#9 is always -1 == octal 777777,,777777
  uint64 zip10;                         // word#10 is always zero.
  uint64 word11:36,:28; // Rotated checksum of words #1. through #10. above.
} ebot;
ebot *U;
//
//      MD5 digest values of a file data BLOB
//
struct md5_ctx ctx;
unsigned char digest[32];
char hashhex[32+1]; // hexadecimal string
char hashm64[32+1]; // modulo 60 xx encoded string
//
//      Globals
//
int verbose=0;
int name_count=0, blob_count=0; // Name Tags and Blobs, model of File System
int record=0;
int leng=0, length=0, type=0, type_look_ahead=0; // DART head prefix
int drn=0; // dart "file" record number, for types -3, 6, or -9.
int serial_number=0;
int bad_text_bit_count=0;
int otnum; // word#24 in Darth

// content counters
struct {int  bits, bytes, nul, newline, ff, space, alnum, other;} ConCount;

// content letter frequency
// Assumed letter rank frequency per classic ETA OIN SRHLD CUM FPG WYB VKX JQZ for English text.
const char* urank=" ETAOINSRHLDCUMFPGWYBVKXJQZ"; // E is rank# 1, Z is rank# 26th in frequency.
char vrank[32]={}; // sampled document's letter frequency ranking
int64 histogram[128]={};
double spearman=0;

const char* taxon_name[]={  "BINARY","ETEXT","OTEXT",  "ERRBLOB","GAP","XOT"};
enum taxon_value{  BINARY,ETEXT,OTEXT,  ERRBLOB,GAP,XOT};
enum taxon_value taxon;

// FILE damage code bits, Reported as hexadecimal value "0xFF" for MYSQL, or empty ""
int damaged=0;
#define logdam(X) damaged|=X
char damrep[16];
void
damage_report(){
  damrep[0]=0;
  if(damaged)sprintf(damrep,"0x%03X",damaged);
}
//
//      DART tape metadata per DART data record
//
char prg[4], prj[4], ppn[8], filnam[8], ext[4];
char ppname[32];
int mode, prot, hidate;
char write_program[16];
char write_ppn[16];
//
//      Date Time stamps ( iso_mdatetime will become the most relevant )
//      created, modified, accessed, dumped
//
int cdate, mdate, adate, ddate;
int        mtime, atime;
//
// Remix Prescience
//
// 1972-11-05 11:59     Tape #0001 BOT is at Noon 5 November 1972, nearly 18 years later
// 1990-08-17 17:08     Tape #3228 the final file ALLDIR.DAT[DMP,SYS] is written.
//                      so the DART records span ten million minutes, since
//                      timestampdiff( minute, '1972-11-05 11:59',' 1990-08-17 17:08' )
//                      is 9,351,669.
//
// De-damage remixing enforces FILE date consistency using the tape reel BOT dates.
// When a FILE mdate is out of range, it defaults to the BOT date for its tape number,
// since that would be the maximum possible date for the file.
//
char iso_bdatetime[32]; // BOT date on previous BOT marker
char iso_cdatetime[32]; // file system RIB alleged "creation" date
char iso_mdatetime[32]; // usually seen file "modification" / "write" date
char iso_adatetime[32]; // "access" date
char iso_ddatetime[32]; // "dump" date
//
// DART record validation
//
uint64 xor_check_tally, xor_check_word;  char *xor_check_result;
uint64 zip_check,kword;
//
// DART record internal markers
//
char word_dsk[8];       // sixbit'DSK   '
char word18[8];         // expect sixbit'DART  ' 444162640000
char word19[8];         //
char wordpend[8];       // expect sixbit'$PEND$' 046045,,564404 at tape[m+length=2]
char word_mcsys[8];
//
// Text editor file from TV and E (almost always) have a page table of contents.
// COMMENT ⊗   VALID 00006 PAGES
// C REC  PAGE   DESCRIPTION
//
#if 0 // use sscanf so this table not used
uint64 E_header[]={
  0416371546612LL,  0472504013100LL,  0201012640630LL,  0446104030140LL,
  0301446020240LL,  0406170551432LL,  0052064051212LL,  0415004050202LL,
  0436124020100LL,  0422132341644LL,  0446412444636LL,  0470321241540LL
};
#endif

// PDP-10 sixbit character decoding tables (and the mod64 xx encoding table)
// SIXBIT tables
//    octal 040                            0100                          0137 octal
//          ↓ •                              ↓                          •   ↓
//         " !"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_"
//
//           1         2         3         4         5         6     Decimal Ruler
//  1234567890123456789012345678901234567890123456789012345678901234
//  0       1       2       3       4       5       6       7      7 Octal Ruler
//  0123456701234567012345670123456701234567012345670123456701234567
//   !"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_ SIXBIT character values
//                              omit comma for bare csv fields
//                                   ↓ omit dot for FILNAM fields
//           Backwhack ↓             ↓ ↓                                       Backwhack ↓
char *sixbit_table= " !\"" "#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ" "[\\]^_";
char *sixbit_fname= " ! "  "#$%&'()*+_-_/0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ" "___^_";
char *sixbit_uname= " ! "  "#$%&____+_-_/0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ" "___^_";
char *sixbit_ppn  = " __"  "_____________0123456789_______ABCDEFGHIJKLMNOPQRSTUVWXYZ" "_____";
char *sixbit_xx   = "+-0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
char *sixbit_rfc  = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-_"; // rfc3548 filename URL safe

// Ugly looking SIXBIT filenames are usually magnetic-tape bit-drop-out data-damage,
// with the exception of the Print Spooler and News Wire temporary file names.
// 'C' as well as SQL string notation must backwhack double quote and backslash
// SAIL filename sanity omits dot and square brackets
// Unix filename sanity omits bash shell special characters

/* ascii SIXBIT decoding functions
 * -------------------------------------------------------------------- *
 * sixbit word into ASCII string 
 * sixbit halfword into ASCII string
 */
char *
sixbit_word_into_ascii(char *p0,pdp10_word w,char *tbl)
{
  char *p=p0;
  // SIXBIT into ASCII by arithmetic would by + 040
  *p++ = tbl[w.sixbit.c1];
  *p++ = tbl[w.sixbit.c2];
  *p++ = tbl[w.sixbit.c3];
  *p++ = tbl[w.sixbit.c4];
  *p++ = tbl[w.sixbit.c5];
  *p++ = tbl[w.sixbit.c6];
  *p++= 0;
  return p0;
}
char *
sixbit_uint_into_ascii(char *p0, uint64 x, char *tbl)
{
  pdp10_word w=(pdp10_word)x;
  char *p=p0;
  // SIXBIT into ASCII by arithmetic would by + 040
  *p++ = tbl[w.sixbit.c1];
  *p++ = tbl[w.sixbit.c2];
  *p++ = tbl[w.sixbit.c3];
  *p++ = tbl[w.sixbit.c4];
  *p++ = tbl[w.sixbit.c5];
  *p++ = tbl[w.sixbit.c6];
  *p++= 0;
  return p0;
}
char *
sixbit_halfword_into_ascii(char *p0,int halfword,char *tbl)
{
  char *p=p0;
  *p++ = tbl[(halfword >> 12) & 077];
  *p++ = tbl[(halfword >>  6) & 077];
  *p++ = tbl[ halfword        & 077];
  *p++ = 0;
  return p0;
}
void
omit_spaces(char *q)
{
  char *t,*p;
  for (p= t= q; *p; p++)
    if (*p != ' ')
      *t++ = *p;
  *t++ = 0;
}

// associative array using hsearch from the 'C' Library.
#define MAXSN 999999 // The early SAILDART collection was at 886465, 2015 numbered 886781 - 154 blob holes.
uchar BIT[]={1,2,4,8,16,32,64,128}; // boolean bit-vector
uchar snseen[1+(MAXSN/8)]={}; // boolean array (used by de-dup to determine when a blob value reappears)
long snmax=1; // next sn ( there is no serial#0 )
long snmax_xot=980000; //    16. xots and up to 3228. bots and eots.
long snmax_err=990000; // 8,318. error blobs
long snmax_gap=999900; //    61. gaps
long check_sn(char *hash){
  ENTRY e,*f;                   // see the 'hsearch' man 3 page
  long value;
  e.key = hash;                 // NAME-key is the digest-hash
  f= hsearch(e,FIND);
  value = ( f ? (long)(f->data) : 0 );
  if(0)fprintf(stderr,"check_sn /%s/ found %ld\n",hash,value);
  return value;
}
long fetch_sn(char *hash){
  ENTRY e,*f;                   // see the 'hsearch' man 3 page
  e.key = hash;                 // NAME-key is the digest-hash
  if(!(f= hsearch(e,FIND))){    // is this blob's hash key in the table ?
    e.key = strdup(hash);       // place copy of hash-key into malloc space
    switch(taxon){
    case ERRBLOB: e.data = (void *)snmax_err++; break;
    case GAP: e.data = (void *)snmax_gap++; break;
    case XOT: e.data = (void *)snmax_xot++; break;
    default: e.data = (void *)snmax++; break;   // coin new VALUE next serial number
    }
    f = hsearch(e,ENTER);
  }
  assert(f);
  return((long)(f->data));
}
// The snhash8 have become the "Accession-Numbering" for this "Digital-Archive".
void load_old_snhash8(){
  ENTRY e,*f;
  FILE *old;
  char *old_snhash8="/large/flat/dart/snhash8.2015";
  long sn,cnt=0;
  errno = 0;
  old = fopen(old_snhash8,"r");
  if (!(old)){
        fprintf(stderr,"Open failed path old_snhash8='%s'\n", old_snhash8);
        exit(1);
  }
  while(EOF != fscanf(old,"%ld,%32ms\n",&sn,&e.key)){
    e.data= (void *)sn;
    //    fprintf(stderr,"%ld,/%s/\n",sn,e.key);
    f = hsearch(e,ENTER);
    assert(f=&e);
    cnt++;
    if(sn>snmax)snmax=sn;
  }
  snmax++; // next available sn
  fprintf(stderr,"DONE load_old_snhash8 cnt=%ld next available sn=%ld\n",cnt,snmax);
}

void
iso_date(char *dest,int sysdate,int systime){
  int day,month,year,hour,minute,second;
  int dpm[]={0,31,28,31, 30,31,30, 31,31,30, 31,30,31}; // days per month
  // 123456789.1234
  // 00-00-00 00:00
  sprintf(dest,"%-20s","null");
  sprintf(dest,"_%6d_%6d_",sysdate,systime);

  // preview
  day   =  sysdate % 31 + 1;
  month = (sysdate / 31) % 12 + 1;  
  year  = (sysdate / 31) / 12 + 1964;
  hour  = systime / 60;
  minute= systime % 60;
  /*
    if(sysdate>0 && ((sysdate < (1968-1964)*372) ||  (sysdate > (1991-1964)*372) || (systime > 1440 ))){
    fprintf(stderr,"%7d / sysdate=%d systime=%d ",record,sysdate,systime);
    fprintf(stderr,"iso_date defect year %d month %d day %d hour %d minute %d\n",year,month,day,hour,minute);
    }  
  */
  if(sysdate < (1968-1964)*372) return; // below floor
  if(sysdate > (1991-1964)*372) return; // above ceiling
  if(systime > 1440 ) return;           // over the wall
  
  // Note 31 times 12 is 372.
  //    sysdate = (year - 1964)*372 + (month-1)*31 + (day-1)
  //    systime = hour*60 + minute
  day   =  sysdate % 31 + 1;
  month = (sysdate / 31) % 12 + 1;  
  year  = (sysdate / 31) / 12 + 1964;

  // Day of month too big ?
  if( day > ((month!=2) ? dpm[month] : (year%4 == 0) ? 29 : 28)) return; // bad day-of-month

  hour = systime / 60;
  minute = systime % 60;
  second = 0;
  // Check for the 23-hour Day Light Savings Spring Forward dates
  // increment one hour for times between 02:00 AM and 02:59 AM inclusive
  switch(sysdate){
  case   920: //  24-Apr-1966
  case  1310: //  30-Apr-1967
  case  1692: //  28-Apr-1968
  case  2075: //  27-Apr-1969
  case  2458: //  26-Apr-1970
  case  2841: //  25-Apr-1971
  case  3230: //  30-Apr-1972
  case  3613: //  29-Apr-1973
  case  3878: //   6-Jan-1974 Nixon oil crisis Daylight-Savings-Time
  case  4311: //  23-Feb-1975 ditto (but Ford was president in 1975)
  case  4761: //  25-Apr-1976
  case  5144: //  24-Apr-1977
  case  5534: //  30-Apr-1978
  case  5917: //  29-Apr-1979
  case  6299: //  27-Apr-1980
  case  6682: //  26-Apr-1981
  case  7065: //  25-Apr-1982
  case  7448: //  24-Apr-1983
  case  7837: //  29-Apr-1984
  case  8220: //  28-Apr-1985
  case  8603: //  27-Apr-1986
  case  8965: //   5-Apr-1987
  case  9347: //   3-Apr-1988
  case  9730: //   2-Apr-1989
  case 10113: //   1-Apr-1990
    if(hour==2) hour++;break; // work around for the impossible datetime stamp values
  default: break;
  }
  // No adjustment for leap seconds.
  // ================================================================================
  // From 1972 to 1991 there were seventeen positive LEAP SECONDS
  // which occured at GMT 00:00:00 on 1 January 1972 to 1980, 1988, 1990, 1991.
  //           and at GMT 00:00:00 on 1 July 1972, 1982, 1983 and 1985.
  // There were no LEAP SECOND in 1984, 1986, 1987 and 1989.
  //    On 1 January 1972 the difference (TAI-UTC) was 10 seconds, and
  //    on 1 January 1991 the difference (TAI-UTC) was 26 seconds.
  // Although NTP Network-Time-Protocol overlaps the SAILDART epoch,
  // the computer date time was normally set from somebody's wristwatch
  // after a building power failure. The PDP10 clock interrupt was driven
  // at 60 hertz by powerline cycles, the Petit electronic clock likely
  // had a crystal oscillator but was set by software based on a wristwatch reading.
  // =================================================================================
  // No adjustment for leap seconds.
  sprintf( dest,"%4d-%02d-%02dT%02d:%02d:%02d",year,month,day,hour,minute,second );
}

void
output_blob_sn(){
  int n,bytcnt,ma,sno;  // Serial-Numbered Output.
  char sn_path[256];
  FILE *snow;           // Serial-Numbered Octal-Word.
  // DATA8
  // Write blob to Serial Numbered path as format data8 (8bpw) eight bytes per PDP10 word.
  errno=0;
  sprintf(sn_path,"/large/data8/sn/%06d",serial_number);
  if(access(sn_path,F_OK)==-1){// Test for Non-Existence
    sno = open( sn_path, O_CREAT | O_WRONLY | O_TRUNC, 0600 );
    if (!(sno>0)){perror("WTF:");fprintf(stderr,"Open failed filename sn_path='%s'\n", sn_path);exit(1);}
    bytcnt = seen * 8;
    n = write( sno, blob, bytcnt );
    assert( n == bytcnt );
    assert(!close( sno ));
  }
  // REMIXED neo DART flat tracks,
  // to make a nearly exact, but much smaller, preservation copy of the SAILDART meme.
  assert( seen >= zcount);
  bytcnt = (seen-zcount) * 8; // Omit zero padding trailer
  if(bytcnt)
    switch( taxon ){
    case BINARY:
      n = write( o_bin, &Tag, sizeof(Tag));
      n = write( o_bin, blob, bytcnt );
      // BINARY OCTAL
      // Write blob to Serial Numbered path as OCTAL text like this "012345670123\n" twelve digits and newline.
      errno=0;
      sprintf(sn_path,"/large/octal/sn/%06d",serial_number);
      if(access(sn_path,F_OK)==-1){// Test for Non-Existence
        snow = fopen(sn_path,"w");
        if (!(snow>0)){perror("WTF:");fprintf(stderr,"Open failed filename sn_path='%s'\n", sn_path);exit(1);}
        for(ma=0;ma<seen;ma++){
          fprintf(snow,"%012llo\n",blob[ma].fw);
        }
        fclose(snow);
      }
      break;
    case ETEXT:
    case OTEXT:
      n = write( o_txt, &Tag, sizeof(Tag));
      n = write( o_txt, blob, bytcnt );
      // TEXT UTF8
      // Write blob to Serial Numbered path as UTF8 text.
      errno=0;
      sprintf(sn_path,"/large/text/sn/%06d",serial_number);
      if(access(sn_path,F_OK)==-1){// Test for Non-Existence
        sno = open( sn_path, O_CREAT | O_WRONLY | O_TRUNC, 0600 );
        if (!(sno>0)){perror("WTF:");fprintf(stderr,"Open failed filename sn_path='%s'\n", sn_path);exit(1);}
        bytcnt = strlen(utf8);
        n = write( sno, utf8, bytcnt );
        assert( n == bytcnt );
        assert(!close( sno ));
      }
      break;    
    case GAP:
      n = write( o_gap, &Tag, sizeof(Tag));
      n = write( o_gap, blob, bytcnt );break;    
    case ERRBLOB:
      n = write( o_err, &Tag, sizeof(Tag));
      n = write( o_err, blob, bytcnt );break;    
    default: break;
    }
}
void
reset_globals(){
  // clear off the global values
  hashhex[0]=hashm64[0]=0;
  seen= 0;
  drn= 0;
  serial_number= 0;
  blob_word_count= 0;
  zcount = 0;
  prot= mode= 0;
  ppname[0]= iso_mdatetime[0]= 0;
  write_ppn[0]= write_program[0]= 0;
  damaged=0;
  taxon=BINARY; // default
  bad_text_bit_count=0;
  otnum=0;
  memset(&Tag,0,sizeof(Tag));
  memset(histogram,0,sizeof(histogram));
  spearman=0;
}

void
decode(){
  // 5486. tape BOT and EOT type=6 records
  if(type==6){
    taxon = XOT;
    drn = record;
    U = (ebot *)V;
    // 16. defective type==6 records (so XOT because it is not a good EOT or BOT).
    if(!(U->class == 2)){
      static int markcnt=1;
      drn = record;
      sprintf(filnam,"MARK%02d",markcnt++);
      strcpy( ext, "ERR");
      strcpy( prj, "XOT");
      strcpy( prg, "ERR");
      sprintf( ppn,    "%3.3s%3.3s",             prj,prg);
      sprintf( ppname, "%3.3s %3.3s %6.6s %3.3s",prj,prg,filnam,ext);
      strcpy(write_program,"-REMIX");
      strcpy(write_ppn,    "ERRBGB");
      strcpy( iso_mdatetime, iso_bdatetime ); // use BOT date
      return;
    }
    sprintf(filnam,"P%05d",U->tapeno);
    strcpy( ext,
            U->headtail == HEAD ? "BOT" :
            U->headtail == TAIL ? "EOT" : "???" );
    sixbit_halfword_into_ascii( prj, U->prj, sixbit_ppn );
    sixbit_halfword_into_ascii( prg, U->prg, sixbit_ppn );
    sprintf( ppn,       "%3.3s%3.3s",             prj,prg);
    sprintf( ppname,    "%3.3s %3.3s %6.6s %3.3s",prj,prg,filnam,ext);
    mdate = U->date_lo | (U->date_hi << 12);
    mtime = U->time;
    iso_date(iso_mdatetime,mdate,mtime); iso_mdatetime[10]=' '; iso_mdatetime[16]=0;
    if( U->tapeno<3000 && (U->headtail == HEAD)){
      strcpy( iso_bdatetime, iso_mdatetime ); // BOT date of pre-MCOPY tape
    }
    return;
  }
  // 61. gap records type=9
  if(type==-9){
    static int gapcnt=1;
    taxon = GAP;
    drn = record;
    sprintf(filnam,"GAP%03d",gapcnt++);
    strcpy( ext, "ERR");
    strcpy( prj, "GAP");
    strcpy( prg, "ERR");
    sprintf( ppn,    "%3.3s%3.3s",             prj,prg);
    sprintf( ppname, "%3.3s %3.3s %6.6s %3.3s",prj,prg,filnam,ext);
    strcpy(write_program,"-REMIX");
    strcpy(write_ppn,    "ERRBGB");
    strcpy( iso_mdatetime, iso_bdatetime ); // use BOT date
    return;
  }

  // File-Start records ONLY past here.
  if(!(type==-3))return;

  drn = record; // File Start record number
  seen = 0;
  damaged = 0;

  // File size word count ( which has proven to be misleading )
  blob_word_count = V->count;

  // Save a copy of the DART record header into a template
  // for validating the File-Continuation Records
  memcpy(template,tape,8*35);

  // Metadata for the SAIL File System (aka Ralph's File System),
  // which I shall christen 'RALFS' pronounced "Ralph's"
  // eponymous for Ralph Gorin, REG, who contributed greatly to its maintenance and preservation.
  // This file system was likely created by accretion from DEC digital equipment software, some
  // portions of which were modified by Saunders, Moorer, Poole, Petit and others prior to the REG era.
  sixbit_uint_into_ascii(       filnam,         V->filnam ,             sixbit_fname );
  sixbit_uint_into_ascii(       write_program,  V->write_program ,      sixbit_fname );
  sixbit_uint_into_ascii(       write_ppn,      V->write_ppn,           sixbit_ppn   );
  sixbit_halfword_into_ascii(   ext,            V->ext ,                sixbit_fname );
  sixbit_halfword_into_ascii(   prj,            V->prj ,                sixbit_ppn   );
  sixbit_halfword_into_ascii(   prg,            V->prg ,                sixbit_ppn   );
  
  sprintf( ppn,         "%3.3s%3.3s",             prj,prg);
  sprintf( ppname,      "%3.3s %3.3s %6.6s %3.3s",prj,prg,filnam,ext);

  mode = V->mode;
  prot = V->prot;

  cdate = V->c_date;                     // 18-bits
  mdate = V->date_lo | (cdate & 070000); // hi order 3-bits from cdate, lo order 12-bits
  adate = V->refdate;
  ddate = V->dumpdate;
  atime = V->reftime;
  mtime = V->time;
  otnum = V->otnum;

  iso_date(iso_cdatetime,cdate,0);      iso_cdatetime[10]=0;
  iso_date(iso_mdatetime,mdate,mtime);  iso_mdatetime[10]=' ';      iso_mdatetime[16]=0;
  iso_date(iso_adatetime,adate,atime);  iso_adatetime[10]=' ';      iso_adatetime[16]=0;
  iso_date(iso_ddatetime,ddate,0);      iso_ddatetime[10]=0;
  
  // When M date is missing, then promote date value from A, C, D or B in that order.
  if( iso_mdatetime[0]=='_' ) logdam(1); // M date defect
  if( iso_mdatetime[0]=='_' ) strcpy( iso_mdatetime, iso_adatetime ); // Access
  if( iso_mdatetime[0]=='_' ) strcpy( iso_mdatetime, iso_cdatetime ); // Create
  if( iso_mdatetime[0]=='_' ) strcpy( iso_mdatetime, iso_ddatetime ); // Dump
  if( iso_mdatetime[0]=='_' ) strcpy( iso_mdatetime, iso_bdatetime ); // BOT

  //  8,318. File Start    *ERROR.ERR
  // 10,052. File Continue *ERROR.ERR
  if(!strcmp(ppname,"ERR OR  *ERROR ERR")){
    static int media_error=1; // rename PRMERR Previous Media Error file
    taxon = ERRBLOB;
    // Remix into FLAT SAIL the size of a (Previous Media Error) blob left by
    // the DART master tape-to-tape copy MCOPY command
    sprintf(filnam,"ME%04d",media_error++);
    strcpy( ext, "ERR");
    strcpy( prj, "PRM");
    strcpy( prg, "ERR");
    sprintf( ppn,    "%3.3s%3.3s",             prj,prg);
    sprintf( ppname, "%3.3s %3.3s %6.6s %3.3s",prj,prg,filnam,ext);
    strcpy( write_program,"-REMIX" );
    strcpy( write_ppn,    "ERRBGB");
    strcpy( iso_mdatetime, iso_bdatetime ); // use BOT date
  }
}

void
damage(){
  int j;
  if( type==-9 || type==6 ){
    fprintf(rib,"%7d / %2d %16s %8d words\n",record,type,ppname,length);
    fprintf(air,"%7d / %2d %16s %8d words\n",record,type,ppname,length);
    fprintf(prm,"%7d / %2d %16s %8d words\n",record,type,ppname,length);
    return;
  }
  if(!(type==-3 || type==0))return; // File (Start or Continue) records only past here
  // diagnostic logs
  fprintf(rib,"%7d / %2d %16s",record,type,ppname); // Retrival Information Block = RIB.        /log/rib
  fprintf(air,"%7d / %2d %16s",record,type,ppname); // dead Air and redundant markers.          /log/air
  fprintf(prm,"%7d / %2d %16s",record,type,ppname); // Previous Media Errors = PRMERR.          /log/prm
  //
  // Verify DART Header record constants
  //
  sixbit_word_into_ascii(word_dsk,tape[1],sixbit_ppn);            // sixbit'DSK   ' 044635300000 or ' ERROR' 004562625762
  sixbit_word_into_ascii(word18,tape[18], sixbit_ppn);            // sixbit'DART  ' 444162640000
  sixbit_word_into_ascii(word19,tape[19], sixbit_fname);          // sixbit'*FILE*' 124651544512 -3 records
  sixbit_word_into_ascii(word19,tape[19], sixbit_fname);          // sixbit'CON  #' 435756000003  0 records
  sixbit_word_into_ascii(wordpend,tape[length-2], sixbit_fname);  // sixbit'$PEND$' 046045564404
  sixbit_word_into_ascii(word_mcsys,tape[21],     sixbit_ppn );   // sixbit' MCSYS' 005543637163
  //
  // These darth defects are in the filename tag, not in the data blob
  //
  if(strcmp( word_dsk,"DSK   "))          logdam(2);
  if(strcmp(   word18,"DART  "))          logdam(2);
  if(type==-3)if(strcmp(word19,"*FILE*")) logdam(2);
  if(type== 0)if(strcmp(word19,"CON  #")) logdam(2);
  if(strcmp(wordpend,  "$PEND$"))         logdam(2);
  if(strcmp(word_mcsys," MCSYS"))         logdam(2);
  //
  // Check the XOR checksum, includes blob data payload
  //
  xor_check_tally = 0;
  xor_check_word = tape[length-1].fw;
  for( j=1; j<=(length-2); j++){
    xor_check_tally ^= tape[j].fw;
  }
  xor_check_result = (xor_check_tally == xor_check_word) ? "" : "xorBAD";
  if (xor_check_tally != xor_check_word) logdam(0x100); // xorBAD
  //
  // check for DAMAGE report,
  // check whether "PRMERR" (previous tape media) errors exist
  //
  zip_check = 0;
  for(j=3;j<=23;j++) zip_check |= tape[length-j].fw;
  zip_check |= tape[25].fw;
  zip_check |= tape[27].fw;
  for(j=29;j<=35;j++) zip_check |= tape[j].fw;
  if (zip_check) logdam(0x200); // zipBAD indicates Previous Media Errors

  // rib
  fprintf(rib," b/%-20s",iso_bdatetime );
  fprintf(rib," m/%-20s",iso_mdatetime );
  fprintf(rib," c/%-20s",iso_cdatetime );
  fprintf(rib," a/%-20s",iso_adatetime );
  fprintf(rib," d/%-20s",iso_ddatetime );
  fprintf(rib," %8llo/DDLOC#%d", (uint64)V->track,6);
  fprintf(rib," %8d/DDLNG#%d",           V->count,7);
  // 8. DREFTM
  // 9. DDMPTM
  for(j=10;j<=17;j++) fprintf(rib," %llo#%d",tape[j].fw,j);
  damage_report();
  fprintf(rib," %s\n",damrep);

  // prmerr
  for(j=25;j>=23;j--) fprintf(prm," %12llo#%d",tape[length-j].fw,-j);
  for(j=22;j>= 3;j--) fprintf(prm," %3llo%d",tape[length-j].fw,-j);
  fprintf(prm," %s\n",damrep);

  // air
  j=18;fprintf(air," %s#18",word18);
  j=19;fprintf(air," %s#19",word19);
  for(j=20;j<=20;j++) fprintf(air," %12llo#%d",tape[j].fw,j);
  j=21;fprintf(air," %s#21",word_mcsys);
  for(j=22;j<=23;j++) fprintf(air," %d,,%d#%d",tape[j].half.left,tape[j].half.right,j);
  for(j=24;j<=27;j++) fprintf(air," %lld#%d",(int64)tape[j].full.word,j);
  for(j=28;j<=28;j++) fprintf(air," %6d#%d",tape[j].half.right,j);
  for(j=29;j<=35;j++) fprintf(air," %llo#%d",tape[j].fw,j);

  if(type== -3)fprintf(air,"\n"); // end-of-line for FILE-START air

  // Only File-Continuation records get PAST here
  if(type!=0)return;
  //
  // compare File-Continue with its File-Start template
  // except for words 0, 19, 20, 24 and 28 which a allowed to differ.
  //
  fprintf(air," ");
  for(j=0;j<=35;j++){
    fprintf(air,"%s",(tape[j].full.word == template[j].full.word) ? "=" : "x"); 
    switch(j){
    case 0:
    case 19:
    case 20:
    case 24:
    case 28: break; // OK for these slots to be different
    default:
      if( tape[j].fw != template[j].fw ){ // Test SAME ?
        logdam(0x020); // file-continuation header Mismatched.
      }
    }
  }
  fprintf(air," %s %s\n",damrep,xor_check_result);
}

// Concatenate the File-Continuation blobs
void
de_frag(){
  // Append payload data words to file content blob
  // Ignore blob_word_count, size of payload determined by record length.
  switch(type){
  case -3:      // file start
  case 0:       // file continue
    memcpy( blob+seen, tape+36, (length-61)*sizeof(pdp10_word) );      
    seen += (length-61);
    break;
  case -9:      // gap
    memcpy( blob+seen, tape+2, (length-2)*sizeof(pdp10_word) );      
    seen += (length-2);
    break;
  case 6:       // tape marker
    assert(length==12);
    memcpy( blob+seen, tape, length*sizeof(pdp10_word));
    seen += length;
    break;
  }
}
// content counters
// struct {int  bits, bytes, nul, newline, ff, space, alnum, other;} ConCount;
double spearman_rank_correlation(){
  double value;
  int64 hits=0, sum=0, chk=0, d;
  int i, j, mx, mj;
  // derive sample document letter ranking from its frequency histogram
  for(i='a';i<='z';i++){
    j = i -'a' + 'A';
    histogram[j] += histogram[i]; // add lowercase into upper counters
    hits += histogram[j];
  }
  for(i=1;i<=26;i++){                   // Foreach capital letter
    mx = -1; // underwater
    for(j=1;j<=26;j++){                 // linear scan
      if( mx < histogram['A'+j-1] ){    // find max count
        mx = histogram['A'+j-1];        // new top dog count
        mj = j;                         // position of dog
      }
    }
    vrank[i] = 'A'+mj-1;      // ASCII code into ranking position
    histogram['A'+mj-1]= -1;  // erase (underwater)
  }
  // evaluate the correlation expression
  sum=0;
  for(i=1;i<=26;i++){
    d = (int)urank[i] - (int)vrank[i];
    sum += d*d;
    chk += d;
  }
  assert(chk==0);
  value = 1. - (6.*(double)sum)/17550.; // 17550. is n*(n*n-1) when n is 26.
  spearman = value;
  if(0)fprintf(stderr,"spearman %6.3lf '%s' "
          "  (%6lld Alpha / %6d Bytes) =%5.1f %% %-7s%5d pages%6d lines%5d lpg  %5d bad35\n",
          spearman, ppname,
          hits, ConCount.bytes,
          ConCount.bytes ? (float)hits*100./(float)ConCount.bytes : 0,
          taxon_name[ taxon ], ConCount.ff+1, ConCount.newline+1,
          (ConCount.newline+1) / (ConCount.ff+1),
          bad_text_bit_count
          );
  return value;
}
void tally(int c){
  ConCount.bytes++;
  ConCount.bits += number_of_bits[c];
  switch(c){
  case 0:               ConCount.nul++;break;
  case '\n':            ConCount.newline++;break;
  case '\f':            ConCount.ff++;break;
  case ' ':             ConCount.space++;break;
  case 'a'...'z':
  case 'A'...'Z':       histogram[c]++;
  case '0'...'9':       ConCount.alnum++;break;
  default:              ConCount.other++;break;
  }
}
void
convert_blob_into_utf8(){
  char *p=utf8;
  char *q=utf8+sizeof(utf8);
  int n,ma;
  int a1,a2,a3,a4,a5;
  int page_count;
  memset(utf8,0,sizeof(utf8));
  memset(&ConCount,0,sizeof(ConCount));
  for(ma=0;ma<seen;ma++)
    if( blob[ma].fw ){
      a1 = blob[ma].seven.a1;
      a2 = blob[ma].seven.a2;
      a3 = blob[ma].seven.a3;
      a4 = blob[ma].seven.a4;
      a5 = blob[ma].seven.a5;
      n = sprintf(p,"%s%s%s%s%s",
                  SAIL_ASCII[ a1 ],
                  SAIL_ASCII[ a2 ],
                  SAIL_ASCII[ a3 ],
                  SAIL_ASCII[ a4 ],
                  SAIL_ASCII[ a5 ]);
      // advance
      p += n;
      assert(p<q);
      // gather statistics
      tally(a1);tally(a2);tally(a3);tally(a4);tally(a5);
      if( blob[ma].seven.bit35 ){
        ConCount.bits++;
        if(!(('0'<=a5 && a5<='9')||a5==' '))    // When final character non-numeric non-space,
          bad_text_bit_count++;                 // not-text file
      }
    }
  // Judgement: Is this blob clean good-looking seven-bit text ?
  n = sscanf(utf8,"COMMENT ⊗   VALID %05d PAGES\n"
             "C REC  PAGE   DESCRIPTION\n"
             "C00001 00001",&page_count);
  if(n==1){
    taxon=ETEXT; // 'E' text table of contents found.
    if( page_count != 1+ConCount.ff ){
      fprintf(stderr,
              "sn=%06d "
              "defective COMMENT ⊗ VALID %05d PAGES vs %05d FormFeeds+1 '%s' %s\n",
              serial_number,
              page_count, 1+ConCount.ff, write_program, ppname );
    }
  }else if(!bad_text_bit_count){
    taxon=OTEXT; // other 'O' text
  }
  spearman_rank_correlation();
}
// omit duplicate blob content from the remix
void
de_dup(){
  int i; char *q;
  unsigned char b,*p;
  uchar newblob=0;
  // This file blob is NOT yet ready. Further records expected.
  if((type==-3 || type==0) && (type_look_ahead==0)){
    return;
  }
  // Blob may be longer or shorter than expected ( log as damaged )
  if( seen>0 && seen != blob_word_count ){
    int under = (seen < blob_word_count );
    logdam( under ? 0x040 : 0x080); // blob_word_count SHORT or LONG
  }
  // Count trailing zero words
  for( zcount=0;
       zcount < seen  &&  blob[ seen-zcount-1 ].fw == 0;
       zcount++ ){
  }
  // Compute an MD5 digest hash and lookup (or assign) to it a serial number.
  bzero(digest,sizeof(digest));
  md5_init_ctx( &ctx );
  md5_process_bytes( blob, seen*8, &ctx );
  md5_finish_ctx( &ctx, digest );
  // Hexadecimal 32-digit character string of numerals 0 to 9 and letters a to f.
  p = digest;
  q = hashhex;
  bzero(hashhex,sizeof(hashhex));
  if(1){
    for (i=0; i<16; i++) // 8-bits each loop cycle
      {
        *q++ = "0123456789abcdef"[(*p & 0xF0 ) >> 4 ];
        *q++ = "0123456789abcdef"[(*p++) & 0xF ];
      }
    hashhex[32]=0;
  }
  // Modulo 64 xx-encoded character string of 22-digits using plus, minus, numerals and 52 alphabetic letters.
  p = digest;
  q = hashm64;
  bzero(hashm64,sizeof(hashm64));
  if(1){
    for (i=0; i<=5; i++) // 24-bits each loop cycle
      {
        /*      */ *q++ = sixbit_xx[                   (*p & 0xFC) >> 2 ];
        b = *p++;  *q++ = sixbit_xx[ (b & 0x03) << 4 | (*p & 0xF0) >> 4 ];
        b = *p++;  *q++ = sixbit_xx[ (b & 0x0F) << 2 | (*p & 0x03)      ];
        b = *p++;  *q++ = sixbit_xx[  b & 0x3F       ];
      }
    hashm64[22]=0;
  }
  newblob=0; // don't know yet
  serial_number = check_sn( 1 ? hashhex : hashm64 );
  if(!( snseen[serial_number/8] & BIT[serial_number%8] )){
    convert_blob_into_utf8();
    newblob=1;
  }
  serial_number = fetch_sn( 1 ? hashhex : hashm64 );    // coin new serial number when needed
  assert( serial_number <= MAXSN );
  snseen[serial_number/8] |= BIT[serial_number%8];      // Set this blob serial number has been SEEN.
  // Write blob content once only
  if(newblob){
    output_blob_sn();
    blob_count++;
    fprintf( snhash,
             "%06d,%s,%s,%s,"
             "%d,%d,%d,"
             "%d,%d,%d,"
             "%d,%d,%d,"
             "%d,%d,%d\n",
             serial_number, hashhex, hashm64, taxon_name[taxon],
             seen, blob_word_count, zcount,
             ConCount.space,
             ConCount.alnum,
             ConCount.other,
             ConCount.bits,
             ConCount.bytes,
             ConCount.nul,
             bad_text_bit_count,
             1+ConCount.ff,
             1+ConCount.newline );
  }
  // Write name tag meta data for each blob occurence (more tags than blobs)
  name_count++;
  fprintf( metadata, "%7d,%4d,%06d,%6s,%s,%s,%6s,%d,%03o_%02o,%s\n",
           drn, otnum, serial_number,
           write_ppn, ppname, iso_mdatetime,
           write_program,
           (prot&022 ? 1:0), // No Read permitted. Read Protected for both local and world.
           prot, mode, damrep );
  reset_globals(); // clear global values
}

int
main(int ac,char **av){
  int bufcnt=0;
  off_t seek_offset=0;
  int iflatdart;
  int n,m=0;
  char *infile="/large/flat/dart/data8";  // default argument #1 original DART format
  int wrdcnt,backwords;
  int64 words=0;
  float GBytes;
  // initialize table for table lookup bit counting
  for(n=16;n<4095;n++){
    // number_of_bits[n] = number_of_bits[n/256]+number_of_bits[(n/16)%16]+number_of_bits[n%16];
    number_of_bits[n] = number_of_bits[n>>8]+number_of_bits[(n>>4)&15]+number_of_bits[n&15];
  }
  // check table for bit counting
  for(n=0;n<127;n++){
    assert(number_of_bits[n] == ((n&1?1:0)+(n&2?1:0)+(n&4?1:0)+(n&8?1:0)+(n&16?1:0)+(n&32?1:0)+(n&64?1:0)));
  }
  // hsearch hash table for the blob digest strings
  hcreate(2*MAXSN);
  load_old_snhash8();
  //
  // Input FILE format is "tape" eight bytes per PDP10 word.
  iflatdart = open(ac>=2 ? av[1] : infile, O_RDONLY);
  if (iflatdart<0){ fprintf(stderr,"ERROR: open file \"%s\" failed.\n",ac>=2 ? av[1] : infile ); return 1; }
  //
  // output FILE format
  // "tags-and-blobs" at eight bytes per PDP10 word.
  o_fil = open("/large/flat/remix/fil", O_CREAT | O_WRONLY | O_TRUNC, 0600);assert(o_fil>0);
  o_txt = open("/large/flat/remix/txt", O_CREAT | O_WRONLY | O_TRUNC, 0600);assert(o_txt>0);
  o_bin = open("/large/flat/remix/bin", O_CREAT | O_WRONLY | O_TRUNC, 0600);assert(o_bin>0);
  o_gap = open("/large/flat/remix/gap", O_CREAT | O_WRONLY | O_TRUNC, 0600);assert(o_gap>0);
  o_err = open("/large/flat/remix/err", O_CREAT | O_WRONLY | O_TRUNC, 0600);assert(o_err>0);
  //
  // output Database Tables
  snhash=fopen("/large/csv/snhash8","w");assert(errno==0);
  assert(snhash);
  metadata=fopen("/large/csv/metadata","w");assert(errno==0);
  metadata2=metadata;
  assert(metadata==metadata2);
  //
  // Bamboo diagnostic feed-forward
  // octal dump the 61. words of a DART file header in three parts named rib, air and prm
  rib=fopen("/large/log/rib","w");assert(errno==0); // disk Retrieval Information Block, Ralph-File-System.
  air=fopen("/large/log/air","w");assert(errno==0); // extra space
  prm=fopen("/large/log/prm","w");assert(errno==0); // Previous Media Errors
  //
  // Read large buffers from flatdart tape 8-byte PDP10 words
  fprintf(stderr,"Begin dart-remix\n");
  while((n= read(iflatdart,&buffer,sizeof(buffer)))){
    if(errno){ fprintf(stderr,"Read ERROR errno=%d\n",errno); return 1; }
    bufcnt++;
    wrdcnt = n/8;
    seek_offset += n;
    words += wrdcnt;
    GBytes = ( words * 8. ) / (1024. * 1024. * 1024. );
    fprintf(stdout,"%12d buffers %12d records  %12lld words   %3lld billion words %8.3f GBytes\n",
            bufcnt,record,words,words/BILLION,GBytes);
    //
    // Process DART record at offset m within the buffer
    while((m+1) < wrdcnt){ // subtle +1 because some -9 gaps are longer than 2^18 words
      //
      // There are two pointers into the 'tape record' named "tape" and "V"
      tape = buffer+m;          // Misnomer, but the word 'tape' is shorter than the word 'record'.
      V = (darth *)(buffer+m);  // DART Header struct Version.
      type = V->type;           // same as "type = tape[0].half.left;"
      //
      // True length of this record
      if(!( type==0 || type==-3 || type==6 || type==-9 )){
        fprintf(stderr,"\n type=%d m=%d wrdcnt=%d record#=%d\n",type,m,wrdcnt,record);
      }
      assert( type==0 || type==-3 || type==6 || type==-9 );
      leng = tape[0].half.right;
      length = (type == -9) ? tape[1].full.word + 2 :  leng + ((type==6) ? 1 : 2);
      //
      // check that the whole record is within the buffer
      if((m+length) > wrdcnt) break; // exit inner loop
      record++;
      // The input file is always the same! The final record will always be at 2937291.
      type_look_ahead = ( record < 2937291 ) ? tape[length].half.left : -1;
      //
      // FIXUP: two defects where type==0 follows a type==6 record.
      if (record==22161 || record==2404328) type=-3; // mark as file START for a headless file
      //
      // Process a DART record
      // Apply 4-D steps to each record
      decode(); // Decode external metadata, look inside the blob later.
      damage(); // Report Current and Previous-Media-Errors. DART code 'PRMERR'. French 'Merde' for 'Media Error'.
      de_frag();// Concatenate record payloads into a data blob.
      de_dup(); // Apply digest-hash (MD5 is good enough) to data blob. Unique data blobs into the REMIX once only.
      //
      // Early exits for testing short run
      if(0) if(record>=1000) goto L9;
      //
      // Advance over the processed record
      m += length;
      length = 0;
    }
    // Early exits for testing short run
    if(0)if(bufcnt>=1)break;

    // Seek backwards to first word of next record
    backwords = length ? (wrdcnt-m) : ((m+1) == wrdcnt) ? 1 : 0;
    if(verbose)fprintf(stderr,"Fall thru with length=%d.  m=%d. wrdcnt=%d.   Seek backwords=%d.\n",
                       length,m,wrdcnt,backwords);
    errno=0;
    seek_offset = -8*backwords;
    lseek(iflatdart,seek_offset,SEEK_CUR); // Seek backwards to first word of next record
    assert(errno==0);
    m=0; // offset of NEXT record in BUFFER
  }
  // Finalization
 L9:
  hdestroy();
  close(iflatdart);
  close(o_fil);  close(o_txt);  close(o_bin);  close(o_gap);  close(o_err);
  fclose(rib);
  fclose(air);
  fclose(prm);
  fclose(snhash);
  fclose(metadata);
  fprintf(stderr,"Totals final\n");
  fprintf(stderr,"%12d buffers %12d records  %12lld words   %3lld billion words %8.3f GBytes\n",
         bufcnt,record,words,words/BILLION,GBytes);
  fprintf(stderr,"DONE dart-remix\n");
  fprintf(stdout,"DONE dart-remix\n");
  return 0;
}
