/* This file is extracted unchanged from the dwww program.
 * dwww is free software.  You may copy it according to the
 * GNU General Public License, version 2.
 */

/*
 * realpath.c -- output the real path of a filename.
 * Lars Wirzenius.
 */
 
#include <sys/param.h>
#include <unistd.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <errno.h>

static char *stripdir(char * dir, char *buf, int maxlen);

int main(int argc, char **argv) {
	char buf[10240];
	int i;
	int err;
	int do_strip;
	
	err = 0;
	do_strip = (argc < 2 || strcmp(argv[1], "-s")) ? 0 : 1;
	
	if (argc < 2 + do_strip) {
		fprintf(stderr, "usage: %s [-s] filename ...\n", argv[0]);
		return 1;
	}

	for (i = 1 + do_strip; i < argc; ++i) {
		if (
			(do_strip && stripdir(argv[i], buf, 10240) == NULL)
	  	     || (!do_strip && realpath(argv[i], buf) == NULL)
		   ) {
			fprintf(stderr, "%s: %s\n", argv[i], strerror(errno));
			fflush(stderr);
			err = 1;
		} else {
		
			printf("%s\n", buf);
			fflush(stdout);
			if (ferror(stdout)) {
				perror("stdout");
				return 1;
			}
		}
	}

	return err;
}


char *stripdir(char * dir, char *buf, int maxlen) {
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
			
		} else if (*in == '.') {
			ldots++;
		} else {
			ldots = 0;
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

