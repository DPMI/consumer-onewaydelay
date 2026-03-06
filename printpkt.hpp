#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <netinet/udp.h>
#include <netinet/ip_icmp.h>
#include <sys/time.h>
#include <arpa/inet.h>

typedef struct{
  u_int32_t exp_id;
  u_int32_t run_id;
  u_int32_t key_id;
  u_int32_t counter;
  u_int64_t starttime;
  u_int64_t stoptime;
  timeval depttime;
  char junk[1500];
}transfer_data;

transfer_data *message; 


/* Not the way to do it. */

struct tg_Protocol {
  u_int32_t exp_id;// Experiment ID
  u_int32_t run_id;// Run ID
  u_int32_t key_id;// Key ID
  u_int32_t counter;// Packet Counter
  u_int64_t starttime;// Start of packet transmission time, comes with packet.counter+1
  u_int64_t stoptime;// Stopt of packet transmission time,  comes with packet.counter+1
  struct timeval depttime; // Departure time. 
  u_int64_t recvstarttime; // Receive start and stop time, recorded at receiver.
  u_int64_t recvstoptime; // Receive start and stop time, recorded at receiver.
  struct timeval recvtime;// Receive time
  // After this comes the payload. 
};

static void print_tg(FILE* dst, const struct tg_Protocol* ptr, bool compact ){  
  struct tg_Protocol h = *(const struct tg_Protocol*)ptr;
  
 
  fprintf(dst, "TG ");
  fprintf(dst, "%d:%d:%d:%d ",ntohl(h.exp_id),ntohl(h.run_id),ntohl(h.key_id),ntohl(h.counter));   
 
  
}


static void print_tcp(FILE* dst, const struct ip* ip, const struct tcphdr* tcp, bool compact ){
  if(!compact){
    fprintf(dst, "TCP(%0x) ", ntohs(ip->ip_len) - 4*tcp->doff - 4*ip->ip_hl);
  } else {
    fprintf(dst, "TCP(HDR[%d]DATA[%0x]) \t [",4*tcp->doff, ntohs(ip->ip_len) - 4*tcp->doff - 4*ip->ip_hl);
    if(tcp->syn) {
      fprintf(dst, "S");
    }
    if(tcp->fin) {
      fprintf(dst, "F");
    }
    if(tcp->ack) {
      fprintf(dst, "A");
    }
    if(tcp->psh) {
      fprintf(dst, "P");
	}
    if(tcp->urg) {
      fprintf(dst, "U");
    }
    if(tcp->rst) {
      fprintf(dst, "R");
    }
    fprintf(dst,"] ");
  }
  fprintf(dst, " %s:%d ",inet_ntoa(ip->ip_src),(u_int16_t)ntohs(tcp->source));
  fprintf(dst, " %s:%d ",inet_ntoa(ip->ip_dst),(u_int16_t)ntohs(tcp->dest));
}

static void print_tcp_ip(FILE* dst, const struct ip* ip, bool compact ){

  const struct tcphdr* tcp = (const struct tcphdr *)((const uint8_t *)ip + (size_t)4*ip->ip_hl); 

  if(!compact){
    fprintf(dst, "TCP(%0x) ", ntohs(ip->ip_len) - 4*tcp->doff - 4*ip->ip_hl);
  } else {
    fprintf(dst, "TCP(HDR[%d]DATA[%0x]) \t [",4*tcp->doff, ntohs(ip->ip_len) - 4*tcp->doff - 4*ip->ip_hl);
    if(tcp->syn) {
      fprintf(dst, "S");
    }
    if(tcp->fin) {
      fprintf(dst, "F");
    }
    if(tcp->ack) {
      fprintf(dst, "A");
    }
    if(tcp->psh) {
      fprintf(dst, "P");
	}
    if(tcp->urg) {
      fprintf(dst, "U");
    }
    if(tcp->rst) {
      fprintf(dst, "R");
    }
    fprintf(dst,"] ");
  }
  fprintf(dst, " %s:%d ",inet_ntoa(ip->ip_src),(u_int16_t)ntohs(tcp->source));
  fprintf(dst, " %s:%d ",inet_ntoa(ip->ip_dst),(u_int16_t)ntohs(tcp->dest));
}


static void print_udp(FILE* dst, const struct ip* ip, const struct udphdr* udp, bool compact){
  if(!compact){
    fprintf(dst, "UDP[%d] %s:%d ",(u_int16_t)(ntohs(udp->len)-8),inet_ntoa(ip->ip_src),(u_int16_t)ntohs(udp->source));
  } else {    
    fprintf(dst, "UDP(HDR[8]DATA[%d])\t %s:%d ",(u_int16_t)(ntohs(udp->len)-8),inet_ntoa(ip->ip_src),(u_int16_t)ntohs(udp->source));
  }
  fprintf(dst, " %s:%d", inet_ntoa(ip->ip_dst),(u_int16_t)ntohs(udp->dest));

  if ( ((u_int16_t)ntohs(udp->dest)>1499  && (u_int16_t)ntohs(udp->dest)<1511) 
       || 
       ((u_int16_t)ntohs(udp->source)>1499  && (u_int16_t)ntohs(udp->source)<1511)
     ) {
    fprintf(dst," tg ");

    const void* payload=(const char*)udp+sizeof(struct udphdr);
    //const void* payload2=(const char*)udp;
  
    message=(transfer_data*)payload;
    fprintf(dst," %u:%u:%u:%u  ", ntohl(message->exp_id),ntohl(message->run_id),ntohl(message->key_id), ntohl(message->counter)); 
    //    fprintf(dst," %u:%u:%u;%u  %p | %p <> %d ", ntohl(message->exp_id),ntohl(message->run_id),ntohl(message->key_id), ntohl(message->counter),payload,payload2, ntohs(udp->len) );
     
  }

}


static void print_udp_ip(FILE* dst, const struct ip* ip, bool compact){

  const struct udphdr* udp = (const struct udphdr *)((const uint8_t *)ip + (size_t)4*ip->ip_hl); 
  if(!compact){
    fprintf(dst, "UDP[%d] %s:%d ",(u_int16_t)(ntohs(udp->len)-8),inet_ntoa(ip->ip_src),(u_int16_t)ntohs(udp->source));
  } else {    
    fprintf(dst, "UDP(HDR[8]DATA[%d])\t %s:%d ",(u_int16_t)(ntohs(udp->len)-8),inet_ntoa(ip->ip_src),(u_int16_t)ntohs(udp->source));
  }
  fprintf(dst, " %s:%d", inet_ntoa(ip->ip_dst),(u_int16_t)ntohs(udp->dest));

  if ( ((u_int16_t)ntohs(udp->dest)>1499  && (u_int16_t)ntohs(udp->dest)<1511) 
       || 
       ((u_int16_t)ntohs(udp->source)>1499  && (u_int16_t)ntohs(udp->source)<1511)
     ) {
    fprintf(dst," tg ");

    const void* payload=(const char*)udp+sizeof(struct udphdr);
    //const void* payload2=(const char*)udp;
  
    message=(transfer_data*)payload;
    fprintf(dst," %u:%u:%u:%u  ", ntohl(message->exp_id),ntohl(message->run_id),ntohl(message->key_id), ntohl(message->counter)); 
    //    fprintf(dst," %u:%u:%u;%u  %p | %p <> %d ", ntohl(message->exp_id),ntohl(message->run_id),ntohl(message->key_id), ntohl(message->counter),payload,payload2, ntohs(udp->len) );
     
  }

}



static void print_icmp(FILE* dst, const struct ip* ip, const struct icmphdr* icmp, bool compact){
  if(!compact) {
	fprintf(dst, "ICMP[%d/%d] %s ", icmp->type, icmp->code,inet_ntoa(ip->ip_src));
	fprintf(dst, " %s ",inet_ntoa(ip->ip_dst));
  } else {
	fprintf(dst, "ICMP \t %s ",inet_ntoa(ip->ip_src));
	fprintf(dst, " %s ",inet_ntoa(ip->ip_dst));
	fprintf(dst, "Type %d , code %d ", icmp->type, icmp->code);
  }

  
  if( icmp->type==0 && icmp->code==0){
    if(!compact){ 
      fprintf(dst, "reply,%d ", ntohs(icmp->un.echo.sequence));
    } else {
      fprintf(dst, " echo reply: SEQNR = %d ", ntohs(icmp->un.echo.sequence));
    }
  }
  if( icmp->type==8 && icmp->code==0){
    if(!compact){
      fprintf(dst, "reqest, %d ", ntohs(icmp->un.echo.sequence));
    } else {
      fprintf(dst, " echo reqest: SEQNR = %d ", ntohs(icmp->un.echo.sequence));
    }
  }
}

static void print_ipv4(FILE* dst, const struct ip* ip, bool compact){
	void* payload = ((char*)ip) + 4*ip->ip_hl;
	fprintf(dst, " IPv4[%d/", 4*ip->ip_hl);
	if(!compact){
	  fprintf(dst, "%d/",(u_int16_t)ntohs(ip->ip_len));
	  fprintf(dst, "%d",(u_int8_t)ip->ip_ttl);
	} else {
	  fprintf(dst, "Len=%d:",(u_int16_t)ntohs(ip->ip_len));
	  fprintf(dst, "ID=%d:",(u_int16_t)ntohs(ip->ip_id));
	  fprintf(dst, "TTL=%d:",(u_int8_t)ip->ip_ttl);
	  fprintf(dst, "Chk=%d:",(u_int16_t)ntohs(ip->ip_sum));
	}
	if(ntohs(ip->ip_off) & IP_DF) {
	  fprintf(dst, "DF");
	}
	if(ntohs(ip->ip_off) & IP_MF) {
	  fprintf(dst, "MF");
	}
	if(!compact){
	  fprintf(dst, "]  ");
	} else {
	  fprintf(dst, " Tos=%0x] \t",(u_int8_t)ip->ip_tos);
	}

	switch( ip->ip_p ) {
	case IPPROTO_TCP:
	  print_tcp(dst, ip, (const struct tcphdr*)payload,compact);
		break;

	case IPPROTO_UDP:
	  print_udp(dst, ip, (const struct udphdr*)payload,compact);
		break;

	case IPPROTO_ICMP:
	  print_icmp(dst, ip, (const struct icmphdr*)payload,compact);
		break;

	case IPPROTO_IGMP:
		fprintf(dst, "IGMP");
		break;

	default:
		fprintf(dst, "Unknown transport protocol: %d \n", ip->ip_p);
		break;
	}
}

static void print_ieee8023(FILE* dst, const struct llc_pdu_sn* llc){
	fprintf(dst,"dsap=%02x ssap=%02x ctrl1 = %02x ctrl2 = %02x\n", llc->dsap, llc->ssap, llc->ctrl_1, llc->ctrl_2);
}

static void print_eth(FILE* dst, const struct ethhdr* eth,bool compact){
	void* payload = ((char*)eth) + sizeof(struct ethhdr);
	uint16_t h_proto = ntohs(eth->h_proto);
	uint16_t vlan_tci;

 begin:

	if(h_proto<0x05DC){
		fprintf(dst, "IEEE802.3 ");
		fprintf(dst, "  %02x:%02x:%02x:%02x:%02x:%02x -> %02x:%02x:%02x:%02x:%02x:%02x ",
		        eth->h_source[0],eth->h_source[1],eth->h_source[2],eth->h_source[3],eth->h_source[4],eth->h_source[5],
		        eth->h_dest[0],  eth->h_dest[1],  eth->h_dest[2],  eth->h_dest[3],  eth->h_dest[4],  eth->h_dest[5]);
		print_ieee8023(dst,(struct llc_pdu_sn*)payload);
	} else {
		switch ( h_proto ){
		case ETHERTYPE_VLAN:
			vlan_tci = ((uint16_t*)payload)[0];
			h_proto = ntohs(((uint16_t*)payload)[0]);
			payload = ((char*)eth) + sizeof(struct ethhdr);
			fprintf(dst, "802.1Q vlan# %d: ", 0x0FFF&ntohs(vlan_tci));
			goto begin;

		case ETHERTYPE_IP:
		  print_ipv4(dst, (struct ip*)payload,compact);
			break;

		case ETHERTYPE_IPV6:
			printf("IPv6 ");
			break;

		case ETHERTYPE_ARP:
			printf("arp ");
			break;

		case 0x0810:
			fprintf(dst, "MP packet ");
			break;

		case STPBRIDGES:
			fprintf(dst, "STP(0x%04x): (spanning-tree for bridges) ", h_proto);
			break;

		case CDPVTP:
			fprintf(dst, "CDP(0x%04x): (CISCO Discovery Protocol) ", h_proto);
			break;

		default:
			fprintf(dst, "Unknown ethernet protocol (0x%04x),  ", h_proto);
			fprintf(dst, " %02x:%02x:%02x:%02x:%02x:%02x -> %02x:%02x:%02x:%02x:%02x:%02x ",
			        eth->h_source[0],eth->h_source[1],eth->h_source[2],eth->h_source[3],eth->h_source[4],eth->h_source[5],
			        eth->h_dest[0],  eth->h_dest[1],  eth->h_dest[2],  eth->h_dest[3],  eth->h_dest[4],  eth->h_dest[5]);
			break;
		}
	}
}
