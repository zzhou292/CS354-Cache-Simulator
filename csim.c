/* Name: Jason Zhou
 * CS login: zhenhao
 * Section(s): LEC 001
 *
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss plus a possible eviction.
 *  2. Instruction loads (I) are ignored.
 *  3. Data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus a possible eviction.
 *
 * The function print_summary() is given to print output.
 * Please use this function to print the number of hits, misses and evictions.
 * This is crucial for the driver to evaluate your work. 
 */

#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include <stdbool.h>

/****************************************************************************/
/***** DO NOT MODIFY THESE VARIABLE NAMES ***********************************/

/* Globals set by command line args */
int s = 0; /* set index bits */
int E = 0; /* associativity */
int b = 0; /* block offset bits */
int verbosity = 0; /* print trace if set */
char* trace_file = NULL;

/* Derived from command line args */
int B; /* block size (bytes) B = 2^b */
int S; /* number of sets S = 2^s In C, you can use the left shift operator */

/* Counters used to record cache statistics */
int hit_cnt = 0;
int miss_cnt = 0;
int evict_cnt = 0;
/*****************************************************************************/


/* Type: Memory address 
 * Use this type whenever dealing with addresses or address masks
 */                    
typedef unsigned long long int mem_addr_t;

/* Type: Cache line
 * 
 * NOTE: 
 * You might (not necessarily though) want to add an extra field to this struct
 * depending on your implementation
 * 
 * For example, to use a linked list based LRU,
 * you might want to have a field "struct cache_line * next" in the struct 
 */                    
typedef struct cache_line {                    
    char valid;         //the valid bot of the line, 0 indicates the line is not usable, 1 indicates usable
    mem_addr_t tag;     //the tag field stores the memory address of the line
    struct cache_line * next;   //next field stores the next line in the set
    int LRUcnt;     //this counter is used to find the LRU line for eviction
} cache_line_t;

typedef cache_line_t* cache_set_t;
typedef cache_set_t* cache_t;


/* The cache we are simulating */
cache_t cache;  

/* init_cache -
 * Allocate data structures to hold info regrading the sets and cache lines
 * use struct "cache_line_t" here
 * Initialize valid and tag field with 0s.
 * use S (= 2^s) and E while allocating the data structures here
 */                    
void init_cache() {
    //calculate number of sets and lines by b and s
    B = 1 << b;
    S = 1 << s;
    
    //allocate space for the entire cache (S of cache_set_t pointer)
    cache = malloc(S*sizeof(cache_set_t));
    //if allocation fails, output error message
    if ( cache == NULL ) {
        printf("Failed to allocate memory for cache");
        exit(1);
    }
    
    //allocate space for each set
    for(int i=0;i<S;i++)
    {
        //initialize space whose size is cache_line_t and assign it to the set
        //this line will be the first line of the corresponding set
        cache_set_t set = malloc(sizeof(cache_line_t));
        //errro handling, if the malloc returns NULL
        if ( set == NULL ) {
            printf("Failed to allocate memory for the set (the first line)");
            exit(1);
        }
        
        //set the first line to this first line allocated
        //the first line is the current line as well
        cache_line_t* cur = set;
        
        //initialize and reserve space for every line in the set
        //there will be total E lines
        for(int j = 1; j<E; j++)
        {
            cur->next = malloc(sizeof(cache_line_t));
            if ( (cur->next) == NULL ) {
                printf("Failed to allocate memory for the line");
                exit(1);
            }
            
            //update valid bit and tag of each line
            
            cur = cur->next;
            
            
            cur->valid = 0;
            cur->tag = 0;
            
            
        }
        
        //update the first line of every set
        cache[i] = set;
        
    }
}


/*
 * maxLRUcnt -
 * Find the maximum LRUcnt read in a set
 * Ideally the input variable iniLine should be the first line in a set
 */
int maxLRUcnt(cache_line_t* iniLine)
    {
        //initialize variables for iteration
        int maxCnt = 0;
        cache_line_t* curLine = iniLine;
        
        while(curLine!=NULL)
        {
            if((curLine->LRUcnt) > maxCnt)
            {
                //if the LRU counter of the current line is larger than
                //the max counter value
                //update the max counter value
                maxCnt = (curLine->LRUcnt);
            }
            
            //check the next line
            curLine = curLine->next;
        }
        
        //return the max counter value
        return maxCnt;
    }
    
/*
 * getLRU -
 * Find the least recently used line in a set
 * By comparing the LRUcnt of each line
 * Return the address of the least recently used line
 */
cache_line_t* getLRU(cache_line_t* iniLine)
    {
        //initialize current count variable
        int curCnt = iniLine->LRUcnt;
        //initialize the target line variable
        //and the iteration pointer
        cache_line_t* tagetLine = iniLine;
        cache_line_t* curLine = iniLine;
        
        while(curLine!=NULL)
        {
            if((curLine->LRUcnt) < curCnt)
            {
                curCnt = curLine->LRUcnt;
                tagetLine = curLine;
            }
            
            curLine = curLine->next;
        }
        
        //return the address of the least recently used line
        return tagetLine;
    }


/*
 * free_cache - free each piece of memory you allocated using malloc
 * inside init_cache() function
 */                    
void free_cache() {
    // local variables used to store the currentline and the nextline
    cache_line_t* currentLine = NULL;
    cache_line_t* nextLine = NULL;
    
    // loop through all sets (all lines)
    for(int i=0;i<S;i++)
    {
        currentLine = cache[i];
        while(currentLine!=NULL){
            nextLine = currentLine->next;
            free(currentLine);
            currentLine = nextLine;
        }
        
        //free the first level pointer to clean the space taken up by the cache pointer
        
    }
    
    free(cache);
}

/*
 * access_data - Access data at memory address addr.
 * If it is already in cache, increase hit_cnt
 * If it is not in cache, bring it in cache, increase miss count.
 * Also increase evict_cnt if a line is evicted.
 * you will manipulate data structures allocated in init_cache() here
 */                    
void access_data(mem_addr_t addr) {
    //first extract tag and set information from the memory address
    mem_addr_t sbits = addr >> b;
    mem_addr_t setinfo = sbits & (S-1);
    
    mem_addr_t tagbits = addr >> (b+s);
    mem_addr_t taginfo = tagbits & ((int)pow(2,64-b-s)-1);
    
    //variables set up: variables need to be used in looping
    mem_addr_t curtag;
    int hit = 0;
    
    cache_line_t* replaceADDR=NULL;

    //start going through the designated set and search for the target
    cache_line_t* first = cache[setinfo];
    cache_line_t* cur = cache[setinfo];
    
    //get the current max LRU count number, this number will be assigned to
    //the line which will be acessed in this function
    int newCntValue = maxLRUcnt(first)+1;
    
    while(cur!=NULL)
    {
        //extract the tag from the address
        curtag = ( cur->tag ) >> (s+b);
        
        //if the tag of the target address matches the current tag and the line is valid
        //this is a hit
        if(taginfo == curtag && (cur->valid) == 1)
        {
            hit = 1;
            //update replaceADDR variable to the address we found
            replaceADDR = cur;
            break;
        }else if(((cur->valid)== 0)&&(replaceADDR==NULL)){
            //else if there's no tag match
            //we find the first invalid line and replace it
            replaceADDR=cur;
        }
        
        cur=cur->next;
    }
    
    if(hit==1){
        //if it's a hit, update the LRU counter to max
        replaceADDR->LRUcnt = newCntValue;
        //update hit counter
        hit_cnt++;
        if(verbosity)
        {
            printf("hit");
        }
    }else{
        if(replaceADDR!=NULL){
            //else if hit == 0, and replaceADDR != NULL
            //It's a miss
            //but there is an invalid line which can be activated and used
            replaceADDR->tag = addr;
            replaceADDR->valid=1;
            replaceADDR->LRUcnt=newCntValue;
            //update miss counter
            miss_cnt++;
            if(verbosity){
                printf("miss");
            }
        }else{
            //else if hit == 0 and replaceADDR == NULL
            //It's a miss and there's no invalud line in this set
            //a used line needs to be evicted and replaced
            replaceADDR = getLRU(first);
            replaceADDR->tag = addr;
            replaceADDR->valid = 1;
            replaceADDR->LRUcnt = newCntValue;
            //update evict counter
            miss_cnt++;
            evict_cnt++;
            if(verbosity){
                printf("miss and evict");
            }
        }
    }
}

/*
 * replay_trace - replays the given trace file against the cache
 * reads the input trace file line by line
 * extracts the type of each memory access : L/S/M
 * YOU MUST TRANSLATE one "L" as a load i.e. 1 memory access
 * YOU MUST TRANSLATE one "S" as a store i.e. 1 memory access
 * YOU MUST TRANSLATE one "M" as a load followed by a store i.e. 2 memory accesses 
 */                    
void replay_trace(char* trace_fn) {                      
    char buf[1000];
    mem_addr_t addr = 0;
    unsigned int len = 0;
    FILE* trace_fp = fopen(trace_fn, "r");

    if (!trace_fp) {
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);
    }

    while (fgets(buf, 1000, trace_fp) != NULL) {
        if (buf[1] == 'S' || buf[1] == 'L' || buf[1] == 'M') {
            sscanf(buf+3, "%llx,%u", &addr, &len);
      
            if (verbosity)
                printf("%c %llx,%u ", buf[1], addr, len);

            // TODO - MISSING CODE
            // now you have: 
            // 1. address accessed in variable - addr
            // 2. type of acccess(S/L/M)  in variable - buf[1] 
            // call access_data function here depending on type of access
            
            //load or save operation will only access data once
            if(buf[1]=='L' || buf[1]=='S')
            {
                access_data(addr);
            }
            
            if(buf[1]=='M')
            {
                //M operation requires two mem access
                access_data(addr);
                access_data(addr);
            }

            if (verbosity)
                printf("\n");
        }
    }

    fclose(trace_fp);
}

/*
 * print_usage - Print usage info
 */                    
void print_usage(char* argv[]) {                 
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}

/*
 * print_summary - Summarize the cache simulation statistics. Student cache simulators
 *                must call this function in order to be properly autograded.
 */                    
void print_summary(int hits, int misses, int evictions) {                
    printf("hits:%d misses:%d evictions:%d\n", hits, misses, evictions);
    FILE* output_fp = fopen(".csim_results", "w");
    assert(output_fp);
    fprintf(output_fp, "%d %d %d\n", hits, misses, evictions);
    fclose(output_fp);
}

/*
 * main - Main routine 
 */                    
int main(int argc, char* argv[]) {                      
    char c;
    
    // Parse the command line arguments: -h, -v, -s, -E, -b, -t 
    while ((c = getopt(argc, argv, "s:E:b:t:vh")) != -1) {
        switch (c) {
            case 'b':
                b = atoi(optarg);
                break;
            case 'E':
                E = atoi(optarg);
                break;
            case 'h':
                print_usage(argv);
                exit(0);
            case 's':
                s = atoi(optarg);
                break;
            case 't':
                trace_file = optarg;
                break;
            case 'v':
                verbosity = 1;
                break;
            default:
                print_usage(argv);
                exit(1);
        }
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        print_usage(argv);
        exit(1);
    }

    /* Initialize cache */
    init_cache();

    replay_trace(trace_file);

    /* Free allocated memory */
    free_cache();

    /* Output the hit and miss statistics for the autograder */
    print_summary(hit_cnt, miss_cnt, evict_cnt);
    return 0;
}
