#define __STDC_FORMAT_MACROS
#include <caputils/caputils.h>
#include <caputils/log.h>

#include <cstring>
#include <ctime>
#include <cstdio>
#include <cstdlib>
#include <cinttypes>
#include <cerrno>
#include <csignal>
#include <cstdint>
#include <getopt.h>

#include <openssl/evp.h>

#include <net/ethernet.h>
#include <netinet/ip.h>
#include <netinet/ip6.h>
#include <netinet/tcp.h>
#include <netinet/udp.h>
#include <arpa/inet.h>

#include <regex.h>
#ifndef REG_STARTEND
#define REG_STARTEND 0x00000400
#endif

#include <string>
#include <map>
#include <vector>
#include <algorithm>


#include <stdint.h>
#include <stddef.h>


#include "printpkt.hpp"

static size_t num_locations = 0;

typedef struct packet_data {
    picotime timestamp;
    std::string location;
} packet_data;

typedef struct packet_id {
    packet_id()
        : seq(0)
        , num(0)
        , data(num_locations){}
    unsigned int seq;
    unsigned int num;
    std::vector<packet_data> data;
} packet_id;

static bool running = true;
static bool verbose = false;
static bool printpkt = false;

static const char* program_name;
static const char* iface = NULL;

static uint32_t seek = 0;         // relative to selected base
static uint32_t count = 1500;     // end relative to selected base (exclusive)
static uint32_t batchSize = 0;
static uint32_t silent = 1;
static unsigned int timeout = 60;

static size_t matched = 0;

static std::map<std::string, packet_id> table; // correlates packets across points
static const struct stream_stat* stream_stat = NULL;

static unsigned int flags = FORMAT_REL_TIMESTAMP;


// ---------------- Base selection ----------------
enum base_t {
    BASE_FRAME = 0,
    BASE_NETWORK,
    BASE_TRANSPORT,
    BASE_PAYLOAD
};

static base_t base_layer = BASE_FRAME;

// ---------------- Regex state ----------------
static char* pattern0 = nullptr;
static char* pattern1 = nullptr;
static char* pattern3 = nullptr;
static bool  regex_mode = false; // true if any pattern is provided

static regex_t preg0, preg1, preg3;
static bool preg0_init=false, preg1_init=false, preg3_init=false;

// ---------------- getopt ----------------
static const char* shortopt = "i:s:c:t:b:hp:y:g:j:k:dv";
static struct option longopt[] = {
    {"iface",        required_argument, 0, 'i'},
    {"base",         required_argument, 0, 'y'},
    {"seek",         required_argument, 0, 's'},
    {"count",        required_argument, 0, 'c'},
    {"pattern",      required_argument, 0, 'g'}, // pattern0 for backward compat
    {"pattern0",     required_argument, 0, 'g'},
    {"pattern1",     required_argument, 0, 'j'},
    {"pattern3",     required_argument, 0, 'k'},
    {"timeout",      required_argument, 0, 't'},
    {"batchsize",    required_argument, 0, 'b'},
    {"help",         no_argument,       0, 'h'},
    {"verbose",      no_argument,       0, 'v'},
    {"displaypkt",   no_argument,       0, 'd'},
    {0,0,0,0}, /* sentinel */
};

static void show_usage(){
    printf("%s\n"
           "usage: %s -i IFACE -s SEEK -c COUNT STREAM..\n"
           "\n"
           " -i, --iface=IFACE      Interface to listen on.\n"
           " -y, --base=<FRAME|IP|TP|PAYLOAD>\n"
           "                        Base layer for seek/count (default FRAME).\n"
           " -s, --seek=BYTES       Byte offset from the selected base.\n"
           " -c, --count=BYTES      End offset from the selected base (exclusive).\n"
           "                        Packet slice is [base+seek, base+count).\n"
           " -g, --pattern0=REGEX   First regex. If any pattern is given, regex mode is on.\n"
           " -j, --pattern1=REGEX   Second regex. ANDed with pattern0.\n"
           " -k, --pattern3=REGEX   Third regex.  ANDed with others.\n"
           "                        In regex mode, packets must match ALL active patterns.\n"
           " -t, --timeout=SEC      Discards packets after SEC.\n"
           " -b, --batchsize=N      Read N packets that *complete* a sequence, then exit.\n"
           " -p N                   Number of points packets are expected to arrive at.\n"
           " -d, --displaypkt       Show packet headers.\n"
           " -v, --verbose          Verbose.\n"
           " -h, --help             This text.\n"
           "\n", program_name, program_name);
    filter_from_argv_usage();
}

template <class T>
T minT(T a, T b){ return a<b?a:b; }

// ---------------- Signals ----------------
static void handle_alarm(int /*signum*/){
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    timepico cur = timespec_to_timepico(ts);

    size_t pruned = 0;
    for ( auto it = table.begin(); it != table.end(); ) {
        const packet_id& id = it->second;
        const bool old = timepico_sub(cur, id.data[0].timestamp).tv_sec > timeout + 5; /* some slack */
        if ( old ) {
            pruned++;
            table.erase(it++);
        } else {
            ++it;
        }
    }

    static char timestr[64];
    time_t t = time(NULL);
    struct tm tm = *localtime(&t);
    strftime(timestr, sizeof(timestr), "%a, %d %b %Y %H:%M:%S %z", &tm);

    if (!silent){
        fprintf(stderr, "%s: [%s] progress report: %'u packets read (%zd matched, %zd pruned, %zd in progress).\n",
                program_name, timestr, (unsigned)0, matched, pruned, table.size());
    }
    matched = 0;
}

static void handle_sigint(int /*signum*/){
    if ( running ){
        fprintf(stderr, "\rGot SIGINT, terminating graceful.\n");
        running = false;
    } else {
        fprintf(stderr, "\rGot SIGINT again, aborting.\n");
        abort();
    }
}

static std::string point_id(const struct cap_header* cp){
    char buf[18];
    sprintf(buf, "%.8s_%.8s", cp->mampid, cp->nic);
    return std::string(buf);
}

static bool packet_sort(const packet_data& a, const packet_data& b) {
    return timecmp(&a.timestamp, &b.timestamp) == -1;
}

static void printPkt(packet_id& pkt, const struct cap_header* cp, bool compact, size_t offset, bool tcp, bool udp){
  if (compact) {
    fprintf(stdout, "%d (%ld) ", pkt.seq, offset);
  } else {
    fprintf(stdout, "%d ", pkt.seq);

  }
  std::sort(pkt.data.begin(), pkt.data.end(), packet_sort);

  for ( unsigned int i = 1; i < num_locations; i++ ){
    const timepico &a = pkt.data[i].timestamp;
    const timepico &b = pkt.data[i-1].timestamp;
    const timepico dt = timepico_sub(a, b);
    fprintf(stdout, " %s %d.%012" PRIu64 " %s %d.%012" PRIu64,
	    pkt.data[i-1].location.c_str(), b.tv_sec, b.tv_psec,
	    pkt.data[i].location.c_str(),   a.tv_sec, a.tv_psec);
    fprintf(stdout, " %d.%012" PRIu64, dt.tv_sec, dt.tv_psec);
  }
  
  if (printpkt){
    if (compact){
      fprintf(stdout, " LINK(%4d) CAPLEN(%4d):", cp->len, cp->caplen);
    }
    fprintf(stdout," ");
    switch(base_layer){
    case BASE_PAYLOAD:
      /* TBD*/
      if (verbose) {
	fprintf(stdout, "|TBD, offset = %ld| ", offset);
      }
      /* Add logic to identify what payload */
      print_tg(stdout, (const struct tg_Protocol*)((const uint8_t *)cp->payload+offset), compact);
      break;
      
    case BASE_TRANSPORT:
      if (tcp) print_tcp_ip(stdout, (const ip*)((const uint8_t *)cp->payload+offset), compact);
      if (udp) print_udp_ip(stdout, (const ip*)((const uint8_t *)cp->payload+offset), compact);
      break;
      
    case BASE_NETWORK:
      print_ipv4(stdout, (const ip*)(cp->ethhdr+offset), compact);
      break;
      
    case BASE_FRAME:
    default:
      print_eth(stdout, cp->ethhdr, compact);
      break;
    } 
  }
  fprintf(stdout, "\n");
}

// ---------------- Layer offset computation (Ethernet + VLAN + IPv4/IPv6 + TCP/UDP) ----------------
static inline uint16_t rd16(const uint8_t* p) {
    uint16_t x;
    std::memcpy(&x, p, sizeof(x));
    return ntohs(x);
}

static void compute_layer_offsets(const struct cap_header* cp,
                                  size_t &l2, size_t &l3, size_t &l4, size_t &l7, bool &tcp, bool &udp)
{
    const uint8_t* frame = (const uint8_t*)cp->payload; // start of captured frame buffer
    size_t caplen = (size_t)cp->caplen;

    l2 = 0; 
    l3 = 0; 
    l4 = 0; 
    l7 = 0;
    tcp = false;
    udp = false;


    if (caplen < sizeof(struct ether_header)) {
        l3 = l4 = l7 = 0; // degenerate, but FRAME base still works
        return;
    }

    size_t off = 0;
    const struct ether_header* eth = (const struct ether_header*)frame;
    uint16_t ethertype = ntohs(eth->ether_type);
    off += sizeof(struct ether_header);

    // Handle stacked VLAN tags (0x8100, 0x88A8, 0x9100)
    while (ethertype == 0x8100 || ethertype == 0x88A8 || ethertype == 0x9100) {
        if (caplen < off + 4) { // TCI(2) + EtherType(2)
            l2 = 0; l3 = 0; l4 = 0; l7 = 0; return; }
        // next ethertype
        ethertype = rd16(frame + off + 2);
        off += 4;
    }

    l2 = 0;
    l3 = off;

    // IPv4
    if (ethertype == 0x0800) {
        if (caplen < l3 + sizeof(struct ip)) { l4 = l7 = l3; return; }
        const uint8_t* ip = frame + l3;
        uint8_t ver_ihl = ip[0];
        uint8_t ihl = (uint8_t)(ver_ihl & 0x0F);
        size_t iphdr_len = (size_t)ihl * 4;
        if (ihl < 5 || caplen < l3 + iphdr_len) { l4 = l7 = l3; return; }

        uint8_t proto = ip[9];
        l4 = l3 + iphdr_len;

        // TCP
        if (proto == IPPROTO_TCP) {
            if (caplen < l4 + sizeof(struct tcphdr)) { l7 = l4; return; }
            const uint8_t* tcp = frame + l4;
            uint8_t data_off = (uint8_t)((tcp[12] >> 4) & 0x0F);
            size_t tcphdr_len = (size_t)data_off * 4;
            if (data_off < 5 || caplen < l4 + tcphdr_len) { l7 = l4; return; }
            l7 = l4 + tcphdr_len;
        }
        // UDP
        else if (proto == IPPROTO_UDP) {
            if (caplen < l4 + 8) { l7 = l4; return; }
            l7 = l4 + 8;
        }
        else {
            l7 = l4; // unknown L4
        }
        return;
    }

    // IPv6
    if (ethertype == 0x86DD) {
        const size_t ipv6_fixed = 40;
        if (caplen < l3 + ipv6_fixed) { 
            l4 = l7 = l3; 
            return; 
        }
        const uint8_t* ip6 = frame + l3;
        uint8_t next = ip6[6];
        l4 = l3 + ipv6_fixed;

        // We keep it simple: do not iterate extension headers.
        if (next == IPPROTO_TCP) {
            tcp = true;
            udp = false;
            if (caplen < l4 + sizeof(struct tcphdr)) { 
                l7 = l4; 
                return; 
            }
            const uint8_t* tcp = frame + l4;
            uint8_t data_off = (uint8_t)((tcp[12] >> 4) & 0x0F);
            size_t tcphdr_len = (size_t)data_off * 4;
            if (data_off < 5 || caplen < l4 + tcphdr_len) { 
                l7 = l4; 
                return; 
            }
            l7 = l4 + tcphdr_len;
        } else if (next == IPPROTO_UDP) {
            tcp = false;
            udp = true;

            if (caplen < l4 + 8) { 
                l7 = l4; 
                return; 
            }
            l7 = l4 + 8;
        } else {
            l7 = l4;
        }
        return;
    }

    // Non-IP – keep L3/L4/L7 conservative
    l4 = l3;
    l7 = l4;
}

#include <cstdio>
#include <cstring>
#include <cstdint>
#include <regex.h>

// ---- FNV-1a 64-bit (stable, fast, allocation-free) ----
static inline uint64_t fnv1a64_bytes(const void* data, size_t len) {
    const unsigned char* p = static_cast<const unsigned char*>(data);
    uint64_t h = 1469598103934665603ull; // offset basis
    for (size_t i = 0; i < len; ++i) {
        h ^= p[i];
        h *= 1099511628211ull;           // FNV prime
    }
    return h;
}

// Extract first capture group if present, else the whole match.
// Returns true if regex matched; false otherwise.
// On success, *out_start points inside `data`, length in *out_len.
static bool regex_extract_first_group_or_span(const regex_t* re,
                                              const unsigned char* data,
                                              size_t len,
                                              const regmatch_t* region, // pass nullptr to use [0,len)
                                              const char** out_start,
                                              size_t* out_len)
{
    if (!re || !data || len == 0) return false;

    // Support up to 8 capture groups + whole match (adjust if you need more)
    regmatch_t m[9];
    std::memset(m, 0, sizeof(m));

    regmatch_t range;
    if (region) {
        range = *region;
    } else {
        range.rm_so = 0;
        range.rm_eo = static_cast<regoff_t>(len);
    }

    // REG_STARTEND lets us pass an arbitrary byte slice (no NUL needed)
    int rc = regexec(re, reinterpret_cast<const char*>(data),
                     static_cast<size_t>(sizeof(m)/sizeof(m[0])),
                     m, REG_STARTEND);
    if (rc != 0) return false;

    // Prefer first capture group
    if (m[1].rm_so != -1 && m[1].rm_eo != -1 && m[1].rm_eo > m[1].rm_so) {
        *out_start = reinterpret_cast<const char*>(data) + m[1].rm_so;
        *out_len   = static_cast<size_t>(m[1].rm_eo - m[1].rm_so);
        return true;
    }

    // Fallback to whole match
    if (m[0].rm_so != -1 && m[0].rm_eo != -1 && m[0].rm_eo > m[0].rm_so) {
        *out_start = reinterpret_cast<const char*>(data) + m[0].rm_so;
        *out_len   = static_cast<size_t>(m[0].rm_eo - m[0].rm_so);
        return true;
    }

    return false;
}

// Append "label=value" (binary-safe value by explicit length) into idbuf.
// Uses '|' as separator between pieces. Truncates if buffer is small.
static void identity_append(char* idbuf, size_t idbuf_sz,
                            const char* label,
                            const char* val, size_t vlen,
                            bool& first_piece)
{
    if (!idbuf || idbuf_sz == 0 || !label || !val) return;
    size_t used = ::strnlen(idbuf, idbuf_sz);
    if (used >= idbuf_sz) return;

    // Separator if not first piece
    if (!first_piece) {
        if (used + 1 < idbuf_sz) {
            idbuf[used++] = '|';
            idbuf[used] = '\0';
        } else return;
    }

    // Append label
    const size_t labellen = std::strlen(label);
    if (used + labellen + 1 >= idbuf_sz) return;  // +1 for '='
    std::memcpy(idbuf + used, label, labellen);
    used += labellen;
    idbuf[used++] = '=';
    idbuf[used] = '\0';

    // Append value (truncate if necessary)
    const size_t space_left = idbuf_sz - used - 1; // keep space for '\0'
    const size_t to_copy = (vlen < space_left) ? vlen : space_left;
    std::memcpy(idbuf + used, val, to_copy);
    used += to_copy;
    idbuf[used] = '\0';

    first_piece = false;
}



// Build identity from all enabled patterns, with caller-defined labels.
// Returns true only if all initialized regexes matched.
// idbuf will contain 'label=value|label=value|...' (may be empty if regex_mode==0)
// *out_hash gets FNV-1a hash of idbuf bytes (0 if empty or if you choose).
static bool regex_match_all_identity(const unsigned char* data, size_t len,
                                     char* idbuf, size_t idbuf_sz,
                                     uint64_t* out_hash)
{
    if (!data || len == 0) return false;

    if (idbuf && idbuf_sz) idbuf[0] = '\0';
    if (out_hash) *out_hash = 0;

    if (!regex_mode) {
        // No regex filtering: treat as matched, but identity empty.
        // If you prefer, you could hash some default or return false here.
        return true;
    }

    bool first_piece = true;

    const char* start = nullptr;
    size_t slen = 0;

    // Map each compiled regex to its logical label (adjust names to your semantics)
    if (preg0_init) {
        if (!regex_extract_first_group_or_span(&preg0, data, len, nullptr, &start, &slen))
            return false;
        identity_append(idbuf, idbuf_sz, "exp_id", start, slen, first_piece);
    }
    if (preg1_init) {
      if (!regex_extract_first_group_or_span(&preg1, data, len, nullptr, &start, &slen)){
	        return false;
	    identity_append(idbuf, idbuf_sz, "key_id", start, slen, first_piece);
      }
    }
    if (preg3_init) {
      if (!regex_extract_first_group_or_span(&preg3, data, len, nullptr, &start, &slen))
	       return false;
      identity_append(idbuf, idbuf_sz, "run_id", start, slen, first_piece);
    }
    
    // If you later add a counter pattern:
    // if (pregX_init) { ... identity_append(..., "counter", ...); }

    // Compute signature from identity string
    if (out_hash && idbuf) {
        size_t idlen = ::strnlen(idbuf, idbuf_sz);
        *out_hash = fnv1a64_bytes(idbuf, idlen);
    }

    return true;
}


// ---------------- Regex matching over binary slice (AND semantics) ----------------
static bool regex_match_all(const unsigned char* data, size_t len)
{
    if (!regex_mode) return true;

    regmatch_t m;
    m.rm_so = 0;
    m.rm_eo = (regoff_t)len;

    if (preg0_init) {
        if (regexec(&preg0, (const char*)data, 1, &m, REG_STARTEND) != 0) return false;
    }
    if (preg1_init) {
        if (regexec(&preg1, (const char*)data, 1, &m, REG_STARTEND) != 0) return false;
    }
    if (preg3_init) {
        if (regexec(&preg3, (const char*)data, 1, &m, REG_STARTEND) != 0) return false;
    }
    return true; // all provided patterns matched
}

static void select_base(const char* base_str){
    if (!base_str) { base_layer = BASE_FRAME; return; }
    if      (!strcasecmp(base_str, "FRAME"))   base_layer = BASE_FRAME;
    else if (!strcasecmp(base_str, "IP"))      base_layer = BASE_NETWORK;
    else if (!strcasecmp(base_str, "TP"))      base_layer = BASE_TRANSPORT;
    else if (!strcasecmp(base_str, "PAYLOAD")) base_layer = BASE_PAYLOAD;
    else {
        fprintf(stderr, "Unknown base: %s (must be FRAME|IP|TP|PAYLOAD)\n", base_str);
        exit(1);
    }
}



int main(int argc, char* argv[]){
    /* extract program name from path. e.g. /path/to/MArCd -> MArCd */
    const char* separator = strrchr(argv[0], '/');
    if ( separator ){
        program_name = separator + 1;
    } else {
        program_name = argv[0];
    }

    struct filter filter;
    if ( filter_from_argv(&argc, argv, &filter) != 0 ){
        exit(1); /* error already shown */
    }

    char *base = 0;

    bool compact = false; 



    int op, option_index;
    while ( (op=getopt_long(argc, argv, shortopt, longopt, &option_index)) != -1 ){
        switch (op){
        case 'i': /* --iface */
            iface = optarg;
            break;
        case 'y':
            base = strdup(optarg);
            break;
        case 'g': /* pattern0 */
            pattern0 = strdup(optarg);
            regex_mode = true;
            break;
        case 'j': /* pattern1 */
            pattern1 = strdup(optarg);
            regex_mode = true;
            break;
        case 'k': /* pattern3 */
            pattern3 = strdup(optarg);
            regex_mode = true;
            break;
        case 's': /* --seek */
            seek = (size_t)atoi(optarg);
            break;
        case 'c': /* --count */
            count = (size_t)atoi(optarg);
            break;
        case 't': /* --timeout */
            timeout = atoi(optarg);
            break;
        case 'p':
            num_locations = atoi(optarg);
            break;
        case 'b':
            batchSize = (uint32_t)atoi(optarg);
            break;
        case 'd':
            printpkt=true;
            break;
        case 'v':
            verbose=true;
            break;
        case 'h': /* --help */
            show_usage();
            exit(0);
        }
    }

    if ( num_locations < 2 ){
        fprintf(stderr, "%s: need at least 2 expected points, use -p to specify.\n", program_name);
    //	exit(1);
    }

    if (base == NULL) {
        base = strndup("FRAME",6);
    }
    select_base(base);

    /* compile regexes if provided */
    if (regex_mode) {
        int rc;
        if (pattern0) { rc = regcomp(&preg0, pattern0, REG_EXTENDED); if (rc==0) preg0_init=true; else { fprintf(stderr, "Invalid regex for -g\n"); exit(1);} }
        if (pattern1) { rc = regcomp(&preg1, pattern1, REG_EXTENDED); if (rc==0) preg1_init=true; else { fprintf(stderr, "Invalid regex for -j\n"); exit(1);} }
        if (pattern3) { rc = regcomp(&preg3, pattern3, REG_EXTENDED); if (rc==0) preg3_init=true; else { fprintf(stderr, "Invalid regex for -k\n"); exit(1);} }
    }

  	/* setup formatter */
	struct format format;
	format_setup(&format, flags);

    struct itimerval tv = {
        {timeout, 0},
        {timeout, 0},
    };
    setitimer(ITIMER_REAL, &tv, NULL);
    signal(SIGALRM, handle_alarm);
    signal(SIGINT, handle_sigint);

    stream_t st;
    if ( stream_from_getopt(&st, argv, optind, argc, iface, NULL, program_name, 0) != 0 ){
        exit(1); /* error already shown */
    }
    stream_stat = stream_get_stat(st);

    unsigned int gseq = 0;

    if (verbose) {
        fprintf(stdout, "VERBOSE = %d\nSeek=%u -- %u \nbatchSize = %u \n", (int)verbose, seek, count, batchSize );
        fprintf(stdout, "base = %s \n", base);
        if (regex_mode) {
            fprintf(stdout, "Regex mode ON. Active patterns:\n");
            if (pattern0) fprintf(stdout, "  pattern0: %s\n", pattern0);
            if (pattern1) fprintf(stdout, "  pattern1: %s\n", pattern1);
            if (pattern3) fprintf(stdout, "  pattern3: %s\n", pattern3);
        } else {
            fprintf(stdout, "Binary content hashing mode (no regex filters).\n");
        }
    }
    uint64_t matched = 0;


    do {
        struct cap_header* cp;
        int ret = stream_read(st, &cp, &filter, NULL);
        if ( ret == EAGAIN ) continue;
        if ( ret == -1 ) break;

        /* Honor filters if provided. */
        if ( filter_match(&filter, cp->payload, cp) ){
			matched++;
		} else {
            continue;
        }

        /* Compute layer offsets */
        size_t l2=0, l3=0, l4=0, l7=0;
        bool tcp=false;
        bool udp=false;


        compute_layer_offsets(cp, l2, l3, l4, l7,tcp, udp);


        /* Base-relative offset window */
        size_t base_offset = 0;
        switch (base_layer) {
            case BASE_FRAME:    base_offset = l2; break;
            case BASE_NETWORK:  base_offset = l3; break;
            case BASE_TRANSPORT:base_offset = l4; break;
            case BASE_PAYLOAD:  base_offset = l7; break;
        }

        if (base_offset > (size_t)cp->caplen) continue;

        size_t start = base_offset + (size_t)seek;
        size_t end   = base_offset + (size_t)count;

        if (start >= (size_t)cp->caplen) continue;
        if (end > (size_t)cp->caplen) end = (size_t)cp->caplen;
        if (end <= start) continue;

        size_t bytes = end - start;

        /* Slice pointer */
        const unsigned char* slice = (const unsigned char*)cp->payload + start;

        char hex[65]={0};
        char identity_buf[256]={0};
        uint64_t identity_sig = 0; 
        unsigned char pktHash[EVP_MAX_MD_SIZE];
        unsigned int hash_len = 0;   
        size_t applied_offset=0;
        std::string hash;
        std::string point;


        /* Apply regex filters if any (AND logic across provided patterns) */
        if (regex_mode) {
	  if (verbose) {
	    fprintf(stdout,"Regex_mode \n");
	  }
	  if (!regex_match_all(slice, bytes)) {
	    continue; // does not satisfy all patterns
	  }
	  
            
	  if (!regex_match_all_identity(reinterpret_cast<const unsigned char*>(cp->payload),
					cp->caplen,
					identity_buf, sizeof(identity_buf),
					&identity_sig)) {
	    // One of the patterns did not match -> drop (AND semantics)
	    if (verbose) {
	      fprintf(stdout,"No match \n");
	    }
	    continue;
	  }

        } else {
	  if (verbose) {
	    fprintf(stdout,"Std_mode \n");
	  }
            /* Calculate SHA-256 over the slice to create a stable correlation key. */
            EVP_Digest(slice, bytes, pktHash, &hash_len, EVP_sha256(), NULL);

            sprintf(hex,
                    "%02x%02x%02x%02x%02x%02x%02x%02x"
                    "%02x%02x%02x%02x%02x%02x%02x%02x"
                    "%02x%02x%02x%02x%02x%02x%02x%02x"
                    "%02x%02x%02x%02x%02x%02x%02x%02x",
                    pktHash[0],  pktHash[1],  pktHash[2],  pktHash[3],
                    pktHash[4],  pktHash[5],  pktHash[6],  pktHash[7],
                    pktHash[8],  pktHash[9],  pktHash[10], pktHash[11],
                    pktHash[12], pktHash[13], pktHash[14], pktHash[15],
                    pktHash[16], pktHash[17], pktHash[18], pktHash[19],
                    pktHash[20], pktHash[21], pktHash[22], pktHash[23],
                    pktHash[24], pktHash[25], pktHash[26], pktHash[27],
                    pktHash[28], pktHash[29], pktHash[30], pktHash[31]);

            hash=hex;
            point = point_id(cp);
            applied_offset=0;

        }


        if ( verbose ) {
            fprintf(stdout, "[%4ld]:%.4s:%.8s:", matched, cp->nic, cp->mampid);
            fprintf(stdout, "LINK(%4d):CAPLEN(%4d):", cp->len, cp->caplen);
	}
	switch(base_layer){
	case BASE_PAYLOAD:
	  /* TBD */
	  applied_offset=l7;
	  break;
	  
	case BASE_TRANSPORT:
	  if (tcp) print_tcp_ip(stdout, (const ip*)((const uint8_t *)cp->payload+l3), compact);
	  if (udp) print_udp_ip(stdout, (const ip*)((const uint8_t *)cp->payload+l3), compact);
	  applied_offset=l4;
	  break;
	  
	case BASE_NETWORK:
	  print_ipv4(stdout, (const ip*)((const uint8_t *)cp->payload+l3), compact);
	  applied_offset=l3;
	  break;
	  
	case BASE_FRAME:
	default:
	  print_eth(stdout, cp->ethhdr, compact);
	  applied_offset=l2;
	  
	  break;
	}
	if ( verbose)  {
            fprintf(stdout," hash=%s base_off=%zu start=%zu end=%zu bytes=%zu\n", hex, base_offset, start, end, bytes);
        }

        auto it = table.find(hash);
        if ( it != table.end() ){ /* match found */
            packet_id& id = it->second;
            /* find duplicates (e.g. same point twice) */
            unsigned int i;
            for ( i = 0; i < id.num; i++ ){
                if ( point == id.data[i].location ){
		  if (verbose) {
		    fprintf(stdout,"Duplicate match, same location. \n");
		  }
		  break;
                }
            }
            if ( i < id.num ) continue;
            id.data[id.num] = {cp->ts, point};

            if ( ++id.num == num_locations ){ /* passed all points */
                matched++;
                if(verbose) {
                    fprintf(stdout,"matched = %d id = %d batchSize = %d \n",(int)matched, id.seq, batchSize);
                }
                if (batchSize>0) {
                    if ( id.seq > batchSize ){
                        running=false;
                    }
                }
                printPkt(id, cp, compact, applied_offset, tcp, udp);
                table.erase(it);
            }
        } else { /* no match */
	  if (verbose) {
	    fprintf(stdout,"Adding packet to list \n");
	  }
            packet_id id;
            id.seq = ++gseq;
            id.num = 1;
            id.data[0] = {cp->ts, point};
            table[hash] = id;
        }
    } while ( running );

    if (preg0_init) regfree(&preg0);
    if (preg1_init) regfree(&preg1);
    if (preg3_init) regfree(&preg3);

    free(base);
    if (pattern0) free(pattern0);
    if (pattern1) free(pattern1);
    if (pattern3) free(pattern3);

    stream_close(st);
    filter_close(&filter);
    return 0;
}
