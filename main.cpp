#define __STDC_FORMAT_MACROS
#include <caputils/caputils.h>
#include <caputils/log.h>
#include <cstring>
#include <ctime>
#include <cstdio>
#include <inttypes.h>
#include <errno.h>
#include <signal.h>
#include <getopt.h>
#include <openssl/md5.h>
#include <netinet/ip.h>
#include <string>
#include <map>
#include <vector>
#include <algorithm>
#include "printpkt.hpp"

static size_t num_locations = 0;

typedef struct packet_data {
	picotime timestamp;
  //	std::string mampid;
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
static uint32_t seek = 0;
static uint32_t count = 1500;
static uint32_t batchSize = 0;
static uint32_t silent = 1;
static unsigned int timeout = 60;
static size_t matched = 0;
static std::map<std::string, packet_id> table; //Out;
//static std::map<std::string, packet_id> tableIn;

static const struct stream_stat* stream_stat = NULL;

static const char* shortopt = "i:s:c:t:b:hp:dv";
static struct option longopt[] = {
	{"iface",      required_argument, 0, 'i'},
	{"seek",       required_argument, 0, 's'},
	{"count",      required_argument, 0, 'c'},
	{"timeout",    required_argument, 0, 't'},
	{"batchsize",  required_argument, 0, 'b'},
	{"help",       no_argument,       0, 'h'},
	{"verbose",    no_argument,       0, 'v'},
	{"displaypkt", no_argument,       0, 'd'},
	{0,0,0,0}, /* sentinel */
};

static void show_usage(){
	printf("%s\n"
	       "usage: %s -i IFACE -s BEGIN -c END STREAM..\n"
	       "\n"
	       "  -i, --iface=IFACE    Interface to listen on.\n"
	       "  -s, --seek=BYTES     Byte offset to begin from.\n"
	       "  -c, --count=BYTES    Byte offset to end.\n"
	       "                       Will look between Seek -- Count bytes. \n"
	       "  -t, --timeout=SEC    Discards packets after SEC.\n"
	       "  -b, --batchsize=N    Read batchsize packets, then exit.\n"
	       "  -p N                 Number of locations packets are expected to arrive at.\n"
	       "  -d, --displaypkt     Show the packets.\n"
	       "  -v, --verbose        Verbose.\n"
	       "  -h, --help           This text.\n"
	       "\n", program_name, program_name);
	filter_from_argv_usage();
}

template <class T>
T min(T a, T b){ return a<b?a:b; }

static void handle_alarm(int signum){
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
	  fprintf(stderr, "%s: [%s] progress report: %'" PRIu64 " packets read (%zd matched, %zd pruned, %zd in progress).\n",
		  program_name, timestr, (long int)0, matched, pruned, table.size());
	}
	matched = 0;
}

static void handle_sigint(int signum){
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

static void format(packet_id& pkt, const struct cap_header* cp, bool compact){
  fprintf(stdout, "%d ", pkt.seq);

	std::sort(pkt.data.begin(), pkt.data.end(), packet_sort);

	for ( unsigned int i = 1; i < num_locations; i++ ){
		const timepico &a = pkt.data[i].timestamp;
		const timepico &b = pkt.data[i-1].timestamp;
		const timepico dt = timepico_sub(a, b);
		fprintf(stdout, " %s %d.%012" PRIu64 " %s %d.%012" PRIu64, pkt.data[i-1].location.c_str(), b.tv_sec, b.tv_psec, pkt.data[i].location.c_str(), a.tv_sec, a.tv_psec);
		fprintf(stdout, " %d.%012" PRIu64, dt.tv_sec, dt.tv_psec);
	}
	if(printpkt){
	  if(compact){
	    fprintf(stdout, " LINK(%4d) CAPLEN(%4d):", cp->len, cp->caplen);
	  }
	  fprintf(stdout," ");
	  print_eth(stdout, cp->ethhdr,compact);
	}
	fprintf(stdout, "\n");
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

	int op, option_index;
	while ( (op=getopt_long(argc, argv, shortopt, longopt, &option_index)) != -1 ){
		switch (op){
		case 'i': /* --iface */
			iface = optarg;
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
		exit(1);
	}

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
	  fprintf(stdout, "VERBOSE = %d\nSeek=%d -- %d \nbatchSize = %d \n", verbose, seek,count,batchSize );
	}

	do {
		struct cap_header* cp;
		int ret = stream_read(st, &cp, &filter, NULL);
		if ( ret == EAGAIN ) continue;
		if ( ret == -1 ) break;

		const size_t offset = min(cp->len, seek);
		const size_t bytes = min(cp->len, min(cp->caplen, count)) - offset;
		if ( offset - bytes < (count<seek) ) continue;

		char hex[33];
		unsigned char* _ = MD5((const unsigned char*)&cp->payload[offset], bytes, NULL);
		sprintf(hex, "%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x",
		        _[0], _[1], _[2], _[3], _[4], _[5], _[6], _[7], _[8], _[9], _[10], _[11], _[12], _[13], _[14], _[15]);

		const std::string hash(hex);
		const std::string point = point_id(cp);

		if ( verbose ) {
			fprintf(stdout, ":%.4s:%.8s:",  cp->nic, cp->mampid);
			fprintf(stdout, "Pkt->LINK(%4d):CAPLEN(%4d):", cp->len, cp->caplen);
			print_eth(stdout, cp->ethhdr,verbose);
			fprintf(stdout,"hash=%s start=%zd, end=%zd\n",hex,offset,bytes);
		}

		
		auto it = table.find(hash);
		if ( it != table.end() ){ /* match found */
		  if(verbose) {
		    fprintf(stdout,"Match \n");
		  }
		  packet_id& id = it->second;
		  
		  /* find duplicates (e.g. arp) */
		  unsigned int i;
		  for ( i = 0; i < id.num; i++ ){
		    if ( point == id.data[i].location ){
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
		    format(id, cp,verbose);
		    table.erase(it);
		  }
		} else { /* no match */
		  if(verbose) {
		    fprintf(stdout,"No match \n");
		  }
		  packet_id id;
		  id.seq = ++gseq;
		  id.num = 1;
		  id.data[0] = {cp->ts, point};
		  table[hash] = id;
		}
		if(verbose) {
		  fprintf(stdout,"Next \n");
		}
	} while ( running );

	stream_close(st);
}
