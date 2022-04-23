#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <math.h>

#define MAX_AGENTS     100
#define NUM_AGENTS     10
#define MAX_HOURS      24
#define MAX_DAYS       365
#define MAX_YEARS      2
#define DAILY_LIMIT    4
#define UNFORGETTER    22e0
#define UNIT_INFO      1e0
#define CUTOFF         0.5e0

#define F_OUT_CONFIG 0x01
#define F_OUT_MATRIX 0x02

typedef struct _relation_set_t {
	size_t    max_persons;
	size_t    num_persons;
	size_t    inc_persons; // for printing config only.
	size_t    time_days;   // for printing config only.
	size_t    daily_limit;
	size_t    max_limit;
	size_t  * couple_list;
	size_t  * num_limits;
	size_t  * schedule;
	size_t  * degree_list;
	double  * closeness;
	double    unit_value;
	double    max_value;
	double    unforgetter;
	double    cutoff_value;
	double    max_closeness;
	double    min_closeness;
} relations_t;

void print_list(const char* name, const size_t* list, size_t n ){

	printf("%s : ",name);
	for( size_t i=0; i<n; i++ ){
		printf("%8d",list[i]);
	}
	printf("\n");
}

void print_matrix( size_t M, size_t N, const double *A, size_t lda ){

        printf("      ");
        for( size_t j=0; j<N; j++ ){
           printf(" %15d",j);
        }
        printf("\n");
        for( size_t i=0; i<M; i++ ){
          printf("%6d",i);
          for( size_t j=0; j<N; j++ ){
            printf(" %15G",*(A+i+j*lda));
          }     
          printf("\n");
        }

}

void make_couples(  relations_t *r ){

	for( size_t i=0; i<r->num_persons; i++ ){
		r->schedule[i] = 0;
		r->couple_list[i] = i; // self-time
	}

	for( size_t i=0; i<r->num_persons; i++ ){
		size_t x = rand();
		size_t j = 0 + x % r->num_persons;
		//printf("rand=%d\n",x);
		if( i == j ) continue; 
		if( r->schedule[i]==0 && r->schedule[j]==0 ){
			r->couple_list[i] = j;
			r->couple_list[j] = i;
			r->schedule[i] = 1;
			r->schedule[j] = 1;
		}
	}

	//print_list("couple_list",r->couple_list,r->num_persons);
	//print_list("schedule   ",r->schedule   ,r->num_persons);

}

void update_relations( relations_t *r ){

	double *c = r->closeness;
	size_t ldc= r->max_persons;
	for( size_t person_id=0; person_id < r->num_persons; person_id++ ){
		size_t couple_id = r->couple_list[person_id];
		if( person_id == couple_id ) continue; // self-meeting
		if( person_id >  couple_id ) continue; // double count
		if( r->num_limits[person_id] <= r->daily_limit && r->num_limits[couple_id] <= r->daily_limit ){
			*( c + couple_id + person_id * ldc ) += r->unit_value;
			*( c + person_id + couple_id * ldc ) += r->unit_value;
			r->num_limits[person_id] += 1;
			r->num_limits[couple_id] += 1;
		}
	}
	if( r->max_limit <= r->daily_limit ){
		r->max_value += r->unit_value;
	}
	//print_list("num_limits ",r->num_limits ,r->num_persons);
}

void forget_relations( relations_t *r ){

	/*
		Forgetting curve ( Ebbinghaus )
		-------------------------------
		b = k/( c*log(t)+k )
			b : savings in [0,1]
			t : time in miniutes

		Formula of half life
		--------------------
		N(t) = N0 * exp(-lambda*t)
		N(t+dt) - N(t) = N0*( exp(-lambda*(t+dt)) - exp(-lambda*t) )
		               = N0*exp(-lambda*t)*( exp(-lambda*dt) - 1 )
		               = N(t)*( exp(-lambda*dt) - 1 )
		N(t+dt) = N(t) * exp(-lambda*dt)

		Forgetting curve ( Approximation )
		-------------------------------
		R(t) = exp(-t/S)
			R : retrievability
			S : stability of memory ( S = 1/lambda )
		R(t+dt) = R(t) * exp( -dt/S )

		S=	22
		dt	r
		1	0.955563036
		2	0.913100716
		3	0.872525293
		4	0.833752918
		5	0.79670347
		6	0.761300387
		7	0.727470509
		8	0.695143928
		9	0.664253843
		10	0.634736419
		11	0.60653066
		12	0.579578279
		13	0.55382358
		14	0.529213342
		15	0.505696707
		16	0.483225081
		17	0.461752026
		18	0.441233168
		19	0.421626105
		20	0.402890322
		21	0.384987099
		22	0.367879441
		23	0.351531996
		24	0.335910981

	*/
	double b = exp(-1e0/r->unforgetter); // numelater is hourly=1, daily=24
	double *c = r->closeness;
	size_t ldc= r->max_persons;
	//double b = exp(-24e0/22e0); // daily
	for( size_t person_id=0; person_id < r->num_persons; person_id++ ){
		for( size_t couple_id=0; couple_id < r->num_persons; couple_id++ ){
			*(c + couple_id + person_id*ldc ) *= b;
			//r->closeness[person_id][couple_id] *= b;
		}	
	}
	r->max_value *= b;
}

void clear_limits( relations_t *r ){

	for( size_t person_id=0; person_id < r->num_persons; person_id++ ){
		r->num_limits[person_id] = 0;
	}
	r->max_limit = 0;
}

size_t compute_degrees( relations_t *r ){

	double *c = r->closeness;
	size_t *d = r->degree_list;
	size_t ldc= r->max_persons;
	double cutoff = r->cutoff_value;
	double xmax=0e0;
	double xmin=r->max_value;
	for( size_t person_id=0; person_id < r->num_persons; person_id++ ){
		d[person_id] = 0;
		for( size_t others_id=0; others_id < r->num_persons; others_id++ ){
			if( person_id == others_id ) continue;
			double x = *(c + others_id + person_id*ldc );
			xmax = ( x > xmax ? x : xmax );
			xmin = ( x < xmin ? x : xmin );
			if( x >= cutoff ){
				d[person_id] += 1;
			}	

		}
	}
	r->max_closeness = xmax;
	r->min_closeness = xmin;

	// compute max degree
	size_t x = 0;
	for( size_t person_id=0; person_id < r->num_persons; person_id++ ){
		size_t y =  r->degree_list[person_id];
		x = ( x < y ? y : x );
	}
	return x;
	
}

void print_config( const relations_t *r ){
	printf("Curr. Number of Persons       : %15d\n",r->num_persons );
	printf("Step Number of Persons        : %15d\n",r->inc_persons );
	printf("Max Number of Persons         : %15d\n",r->max_persons );
	printf("Hourly Exchanged Informaion   : %15G\n",r->unit_value  );
	printf("Unforgetting Parameter        : %15G\n",r->unforgetter );
	printf("Daily Unforgatting Ratio      : %15G\n",exp(-24e0/r->unforgetter));
	printf("Daily Limit of Comm. times    : %15d\n",r->daily_limit );
	printf("Cutoff for Closeness          : %15G\n",r->cutoff_value);
	printf("Days for Simulations          : %15d\n",r->time_days   );
}

static void usage(){
        printf("usage :\n");
        printf("  dumber [-i <num_persons>] [-s <num_persons>] [-n <num_persons>] \n");
        printf("         [-l <daily_limit>] [-v <unit_value>] [-u <unforget>] [-c <cutoff>] [-t <days>]\n");
        printf("         [-o {all|config|matrix}] [-h]\n\n");
        printf("\n");
        printf("  Agent controll:\n");
        printf("     -i <num_persons>    : integer, inittial number of persons to repetition (default=none)\n");
        printf("     -s <num_persons>    : integer, increasing number of persons in a repetition step (default=1)\n");
        printf("     -n <num_persons>    : integer, (final) number of persons in this simulation (default=%d)\n",MAX_AGENTS);
        printf("\n");
        printf("  Simulation controll:\n");
        printf("     -l <daily_limit>    : integer, upper limit for number of meetings in a day (default=%d)\n",DAILY_LIMIT);
        printf("     -v <unit_value>     : real, information quontity exchanging in a meeting (default:%G)\n",UNIT_INFO);
        printf("     -u <unforget>       : real, unforgeting stabilizer for forgetting curve. if <unforget> is larger, the curve is more stable. (default:%G)\n",UNFORGETTER);
        printf("     -c <cutoff>         : real, lower cutoff to judge a connection between two persons (default=%G)\n",CUTOFF);
        printf("\n");
        printf("  Evolution controll:\n");
        printf("     -t <days>           : integer, period of simulation in days (default=%d)\n",MAX_DAYS*MAX_YEARS);
        printf("\n");
        printf("  Output controll:\n");
        printf("     -o all              : print the simulation configuration and the final relation matrix\n");
        printf("     -o config           : print the simulation configuration\n");
        printf("     -o matrix           : print the final relation matrix\n");
        printf("\n");
}

int main( int argc, char** argv ){

        // option paramters
	size_t init_agents=0;
	size_t step_agents=1;
	size_t nagents=MAX_AGENTS;
	size_t dlimit =DAILY_LIMIT;
	double uvalue =UNIT_INFO;
	double fstable=UNFORGETTER;
	double cutoff =CUTOFF;
	size_t tdays  =MAX_DAYS*MAX_YEARS;
	size_t oflag = 0;

        // processing command option
        char*  argend;
        opterr = 0;
        int flags = 0;
        int c;
        while((c=getopt(argc,argv,"i:s:n:l:v:t:u:c:o:h")) != -1 ){
                switch(c){
                case 'i' : init_agents = strtol(optarg,&argend,10);if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 's' : step_agents = strtol(optarg,&argend,10);if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 'n' : nagents = strtol(optarg,&argend,10);if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 'l' : dlimit  = strtol(optarg,&argend,10);if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 't' : tdays   = strtol(optarg,&argend,10);if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 'v' : uvalue  = strtod(optarg,&argend)   ;if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 'u' : fstable = strtod(optarg,&argend)   ;if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 'c' : cutoff  = strtod(optarg,&argend)   ;if( *argend != '\0' ){ usage(); return -1; }; break;  
                case 'o' :
                        if     ( strncmp(optarg,"all"   ,3)==0 ){ oflag=(F_OUT_CONFIG|F_OUT_MATRIX); }
                        else if( strncmp(optarg,"config",6)==0 ){ oflag=F_OUT_CONFIG; }
                        else if( strncmp(optarg,"matrix",6)==0 ){ oflag=F_OUT_MATRIX; }
                        else { usage(); return -1; }
                        break;

                case 'h' : usage(); return 0; 
                default  :
                        printf("Option Error : %c\n",c);
                        usage();
                        return -1;
                }
        }

	double* closeness = calloc(nagents*nagents,sizeof(double));
	size_t* couples   = calloc(nagents,sizeof(double));
	size_t* num_limits= calloc(nagents,sizeof(double));
	size_t* schedule  = calloc(nagents,sizeof(double));
	size_t* degrees   = calloc(nagents,sizeof(double));

	if( init_agents == 0 ) init_agents = nagents;

	relations_t relations;

	relations.max_persons = nagents;
	relations.num_persons = init_agents;
	relations.inc_persons = step_agents;
	relations.time_days   = tdays;
	relations.daily_limit = dlimit;
	relations.couple_list = couples;
	relations.num_limits  = num_limits;
	relations.schedule    = schedule;
	relations.degree_list = degrees;
	relations.closeness   = closeness;
	relations.unit_value  = uvalue;
	relations.unforgetter = fstable;
	relations.cutoff_value= cutoff;
	relations.max_limit   = 0;
	relations.max_value   = 0e0;

	if( oflag & F_OUT_CONFIG ){
		printf("SIMULATION CONFIGURATION:\n");
		print_config( &relations );
        	printf("\n");
	}

	// seed for rundom generator
	srand((unsigned int)time(NULL));


	// Time Evolution
	printf("SIMULATION RESULTS:\n");
	printf(" persons,   dumber,   max closeness,   min closeness\n");
	for( size_t i = init_agents; i <= nagents; i+=step_agents ){
		relations.num_persons = i;
		for( size_t t_day  = 0; t_day  < tdays ; t_day ++ ){
			for( size_t t_hour = 0; t_hour < MAX_HOURS; t_hour++ ){

				// make coupling-ID list
				make_couples( &relations );

				// update relations
				update_relations( &relations );

				// forget relations
				forget_relations( &relations );

			}
			clear_limits( &relations );
		}
		size_t dumber = compute_degrees( &relations );
		printf("%8d, %8d, %15G, %15G\n",i,dumber,relations.max_closeness,relations.min_closeness);
	}

	//printf("max value = %G\n",relations.max_value);
	if( oflag & F_OUT_MATRIX ){
        	printf("\n");
		printf("FINAL RELATION MATRIX:\n");
		print_matrix( relations.num_persons, relations.num_persons, relations.closeness, relations.max_persons );
        	printf("\n");
	}

	free(closeness );
	free(couples   );
	free(num_limits);
	free(schedule  );
	free(degrees   );

	return 0;
}
