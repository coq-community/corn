/* This file is extracted unchanged from the dwww program.
 * dwww is free software. You can redistribute it and/or modify
 * it under the terms of the GNU General Public License, version 2, as
 * published by the Free Software Foundation.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

/*
 * realpath.c -- output the real path of a filename.
 * Lars Wirzenius.
 */

#define _GNU_SOURCE
#include <sys/param.h>
#include <unistd.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <getopt.h>
#include <stdarg.h>

static char *stripdir(char * dir, char *buf, int maxlen);

int option_strip = 0; /* do stripdir */
int option_zero  = 0; /* output zero terminated */
char * myname    = "";
extern int optind;

static const struct option long_options []  = {
    {"strip", 	no_argument, 	NULL, 's'},
    {"zero", 	no_argument, 	NULL, 'z'},
    {"help", 	no_argument, 	NULL, 'h'},
    {"version",	no_argument, 	NULL, 'v'},
    {0,		0, 		0,     0 }
};
static const char *short_options = "szhv?";

static void error( char * fmt, ...  ) {
	va_list list;

	va_start(list, fmt);
	vfprintf(stderr, fmt, list);
	fflush(stderr);
	va_end(list);
}


static void show_usage( int exit_code ) {
	error( "Usage:\n"
		" %s [-s|--strip] [-z|--zero] filename ...\n"
		" %s -h|--help\n"
		" %s -v|--version\n", myname, myname, myname);
	exit( exit_code );
}

static void show_version( int exit_code ) {
	error("%s version %s\n", myname, VERSION);
	exit ( exit_code );
}

		

static void parse_options(int argc, char ** argv ) {
	int c, opt_idx;
	
	while ((c = getopt_long( argc, 
				 argv, 
				 short_options,
				 long_options,
				 &opt_idx )) != EOF ) {
		switch (c) {
			case 's':
				option_strip = 1;
				break;
			case 'z':
				option_zero = 1;
				break;
			case 'v':
				show_version( 0 );
				/* NOT REACHED */
			case 'h':
			case '?':
				show_usage( 0 );
				/* NOT REACHED */
			default:
				error("%s: Unknown option: %c\n", myname, c);
				show_usage( 2 );
				/* NOT REACHED */
		}
	}

	if ( optind == argc ) {
		error("%s: need at least one filename\n", myname);
		show_usage(2);
		/* NOT REACHED */
	}
}
	

	
int main(int argc, char **argv) {
	char buf[10240];
	char * p;
	int status = 0;
	char * ok;

	myname = ( p = strchr(argv[0], '/') ) ? p+1 : argv[0];

	parse_options(argc, argv);

	while (optind < argc) {
		if (option_strip) {
			ok = stripdir( argv[optind], buf, sizeof(buf));
		} else {
			ok = realpath(argv[optind], buf);
		}
		if (!ok) {
			error( "%s: %s\n", argv[optind], strerror(errno));
			status = 1;
		} else {
			fprintf(stdout, "%s", buf);
			putc(option_zero ? '\0' : '\n', stdout);
			fflush(stdout);
			if (ferror(stdout)) {
				error("error writing to stdout: %s\n", strerror(errno));
				exit( 3 );
			}
		}
		optind++;
	}
	return status;
}


static char *stripdir(char * dir, char *buf, int maxlen) {
	char * in, * out;
	char * last;
	int ldots;

	in   = dir;
	out  = buf;
	last = buf + maxlen; 
	ldots = 0;
	*out  = 0;
       	
	
	if (*in != '/') {
		if (getcwd(buf, maxlen - 2) ) {
			out = buf + strlen(buf) - 1;
			if (*out != '/') *(++out) = '/';
			out++;
		}
		else
			return NULL;
	}

	while (out < last) {
		*out = *in;

		if (*in == '/')
		{
			while (*(++in) == '/') ;
			in--;
		}		

		if (*in == '/' || !*in)
		{
			if (ldots == 1 || ldots == 2) {
				while (ldots > 0 && --out > buf)
				{
					if (*out == '/')
						ldots--;
				}
				*(out+1) = 0;
			}
			ldots = 0;
			
		} else if (*in == '.' && ldots > -1) {
			ldots++;
		} else {
			ldots = -1; 
		}
		
		out++;

		if (!*in)
			break;
		
		in++;
	}

	if (*in) {
		errno = ENOMEM;
		return NULL;
	}
	
	while (--out != buf && (*out == '/' || !*out)) *out=0;
	return buf;
}

