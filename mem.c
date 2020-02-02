/*
 *      mem.c           logo memory management module           dvb 6/28/88
 *
 *	Copyright (C) 1993 by the Regents of the University of California
 *
 *      This program is free software: you can redistribute it and/or modify
 *      it under the terms of the GNU General Public License as published by
 *      the Free Software Foundation, either version 3 of the License, or
 *      (at your option) any later version.
 *
 *      This program is distributed in the hope that it will be useful,
 *      but WITHOUT ANY WARRANTY; without even the implied warranty of
 *      MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *      GNU General Public License for more details.
 *
 *      You should have received a copy of the GNU General Public License
 *      along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

#include <assert.h>
#include <stdarg.h>

#define WANT_EVAL_REGS 1
#include "logo.h"
#include "globals.h"
extern NODE *stack, *numstack, *expresn, *val, *parm, *catch_tag, *arg;

/* #ifdef ibm */
/* #ifndef __RZTC__ */
/* #include <alloc.h> */
/* #endif */
/* #endif */

#ifdef PUNY
#define GCMAX 1000
#else
#ifdef THINK_C
#define GCMAX 8000
#else
#ifdef __RZTC__
#define GCMAX 3000
#else
#define GCMAX 16000

#endif
#endif
#endif

static void mark(NODE *);
static void gc(BOOLEAN);

#ifdef THINK_C
extern NODE *gcstack[];
#else
NODE *gcstack[GCMAX];
#endif

NODE **mark_gcstack = gcstack;
NODE **gctop = gcstack;
NODE **gcbottom = gcstack;

long int mem_nodes = 0, mem_max = 0;	/* for Logo NODES primitive */

/* GC heuristic parameters. These parameters can be modified to fine tune
   the performance of the GC program. The values below are a good set of
   default parameters that should work well for most data */

/* Number of times to collect at the current GC state before going to
   the next state. Basically the number of times a given generation is
   collected before its members are moved to an older generation */
#define gc_age_threshold 4

FIXNUM seg_size = SEG_SIZE;

/* A new segment of nodes is added if fewer than freed_threshold nodes are
   freed in one GC run */
#define freed_threshold ((long int)(seg_size * 0.4))

#define NUM_SEGMENTS    256
NODE *free_list = NIL;                  /* global ptr to free node list */
struct segment *segment_list = NULL;    /* global ptr to segment list */
NODE *segment_bases[NUM_SEGMENTS];      /* addresses of nodes[0] */
int num_segment_bases = 0;              /* number of segments allocated */

long int mem_allocated = 0, mem_freed = 0;

/* The number of generations */
#define NUM_GENS 4

/* ptr to list of Nodes in the same generation */
// NODE *generation[NUM_GENS] = {NIL};
ZPTRTYPE generation[NUM_GENS] = {0};

/* ptr to list of nodes that point to younger nodes */
BOOLEAN oldyoungs_dirty = FALSE;
#define DEBUGSTREAM     (dribblestream ? dribblestream : stdout)

#define MAX_NODEPTRS    2048

struct oldyoung {
    struct oldyoung *next;
    int    num_nodes;
    NODE  *nodes[MAX_NODEPTRS];
};

struct oldyoung *oldyoung_list = NULL;
struct oldyoung *oldyoung_free = NULL;
#ifdef MEM_STATS
int num_oldyoung_segments = 0;
int num_gc_full = 0, num_gc_incr = 0;
int num_newnode = 0;
#endif

static BOOLEAN check_pointer (volatile NODE *ptr_val);

#if 0
#define zipPTR(p)       ((p)?(((p)-segment_bases[(p)->segment_base])<<8)+(p)->segment_base:0)
#define unzipPTR(x)     ((x)?segment_bases[(NUM_SEGMENTS-1)&(x)]+((x)>>8):0)
#endif

#ifdef __LP64__

static ZPTRTYPE zipPTR(NODE *ptr) {
    int segment_base;
    ZPTRTYPE ret;
#ifndef NDEBUG
    struct segment *segment;
#endif

    if (NIL == ptr) return 0;
    assert(check_pointer(ptr));
    segment_base = ptr->segment_base;
    assert(segment_base < num_segment_bases);
    ret = (ptr - segment_bases[segment_base]);
#ifndef NDEBUG
    segment = (struct segment *)(segment_bases[segment_base] - 1);
    assert(ret < segment->u.header.size);
#endif
    ret = (ret << 8) + segment_base;
    return ret;
}

static NODE *unzipPTR(ZPTRTYPE ptr) {
    NODE *ret;
    int segment_base;
#ifndef NDEBUG
    struct segment *segment;
#endif

    if (0 == ptr) return NIL;
    segment_base = (NUM_SEGMENTS - 1) & ptr;
    assert(segment_base < num_segment_bases);
    ret = segment_bases[segment_base];
    assert(segment_base == ret->segment_base);
#ifndef NDEBUG
    segment = (struct segment *)(segment_bases[segment_base] - 1);
    assert((ptr >> 8) < segment->u.header.size);
#endif
    ret = ret + (ptr >> 8);
    assert(check_pointer(ret));
    return ret;
}

#else

#define zipPTR(x)       x
#define unzipPTR(x)     x

#endif

static struct oldyoung *addoldyoungseg(void) {
    struct oldyoung *seg;

    seg = (struct oldyoung*)malloc(sizeof(struct oldyoung));
    if (NULL == seg)
        err_logo(OUT_OF_MEM_UNREC, NIL);
    seg->num_nodes = 0;
    seg->next = NULL;
#ifdef MEM_STATS
    num_oldyoung_segments++;
#endif
    return seg;
}

static void add_oldyoung(NODE *ptr) {
    for (;;) {
        if (oldyoung_free->num_nodes < MAX_NODEPTRS) {
            ptr->gc.oldyoung = 1;
            oldyoung_free->nodes[oldyoung_free->num_nodes++] = ptr;
            return;
        }
        if (NULL == oldyoung_free->next) {
            oldyoung_free->next = addoldyoungseg();
        }
        oldyoung_free = oldyoung_free->next;
    }
}

#define GC_NOTMARKED    0
#define GC_GCTWA        255

unsigned char current_gc = 0;

long int gc_stack_malloced = 0;

long int gc_stack_size = GCMAX;

long int gc_overflow_flag = 0;

NODE *reserve_tank = NIL;

BOOLEAN inside_gc = 0, int_during_gc = 0;

int next_gen_gc = 0, max_gen = 0;

int mark_gen_gc;

#if 0
#define GC_DEBUG 1 /* */
#define GC_TWOBYTE 1 /* Use 2-byte stack offset in mark phase */
#endif

#ifdef GC_DEBUG
long int num_examined, num_visited;
#endif

NODE *lsetsegsz(NODE *args) {
    NODE *num = pos_int_arg(args);
    FIXNUM val;

    if (NOT_THROWING) {
        val = getint(num);
        if (1024 <= val && val <= (16*1024*1024)) {
	    seg_size = val;
        } else
            err_logo(BAD_DATA_UNREC, num);
    }
    return UNBOUND;
}

static BOOLEAN addseg(void) {
    long int p;
    struct segment *newseg;
    // unsigned long ptr;

    if (NUM_SEGMENTS == num_segment_bases) /* segment_bases[] array is full? */
        return 0;

    newseg = (struct segment *)malloc(sizeof(struct segment)
					   + (seg_size - 1)
                                           * sizeof(struct logo_node));
    if (newseg != NULL) {
        newseg->u.header.next = segment_list;
	newseg->u.header.size = seg_size;
        segment_list = newseg;
        // ptr = (unsigned long)&(newseg->nodes[0]);
        // fprintf(stderr,"addseg: %016lx\n",ptr);
        for (p = 0; p < seg_size; p++) {
            newseg->nodes[p].nunion.next_free = free_list;
            free_list = &(newseg->nodes[p]);
	    settype(&(newseg->nodes[p]), NTFREE);
            newseg->nodes[p].segment_base = num_segment_bases;
	}
        segment_bases[num_segment_bases++] = &(newseg->nodes[0]);
	return 1;
    }
    return 0;
}

static void clear_mark_gc(void) {
    struct segment *seg;
    int p;
    NODE *ptr;

    for (seg = segment_list; seg; seg = seg->u.header.next) {
        for (p = 0; p < seg->u.header.size; p++) {
            ptr = &(seg->nodes[p]);
            if (NTFREE == ptr->node_type ||
                GC_GCTWA == ptr->mark_gc) continue;
            ptr->mark_gc = GC_NOTMARKED;
        }
    }
}


#ifdef THINK_C
#pragma options(!global_optimizer)
#endif
#ifdef WIN32
#pragma optimize("",off)
#endif
/* Think C tries to load ptr_val->node_type early if optimized */

#define NILP(x)         (NIL == (x))

#define GC_OPT          1

#ifdef GC_OPT
#define VALID_PTR(x)    (!NILP(x))
#else
#define VALID_PTR(x)    (valid_pointer(x))
#endif

static BOOLEAN check_pointer (volatile NODE *ptr_val) {
    struct segment* current_seg;
    unsigned long int ptr = (unsigned long int)ptr_val;
    FIXNUM size;
   
    if (ptr_val == NIL) return 0;
    for (current_seg = segment_list; current_seg != NULL;
		current_seg = current_seg->u.header.next) {
	size = current_seg->u.header.size;
	if ((ptr >= (unsigned long int)&(current_seg->nodes[0])) &&
	    (ptr <= (unsigned long int)&(current_seg->nodes[size-1])) &&
	    ((ptr - (unsigned long int)&(current_seg->nodes[0]))%
	                 (sizeof(struct logo_node)) == 0))
	    return 1;
    }
    return 0;
}

static BOOLEAN valid_pointer (volatile NODE *ptr_val) {
    struct segment* current_seg;
    unsigned long int ptr = (unsigned long int)ptr_val;
    FIXNUM size;
   
    if (ptr_val == NIL) return 0;
    for (current_seg = segment_list; current_seg != NULL;
		current_seg = current_seg->u.header.next) {
	size = current_seg->u.header.size;
	if ((ptr >= (unsigned long int)&(current_seg->nodes[0])) &&
	    (ptr <= (unsigned long int)&(current_seg->nodes[size-1])) &&
	    ((ptr - (unsigned long int)&(current_seg->nodes[0]))%
	                 (sizeof(struct logo_node)) == 0))
	    return (ptr_val->node_type != NTFREE);
    }
    return 0;
}

#ifdef THINK_C
#pragma options(global_optimizer)
#endif
#ifdef WIN32
/* #pragma optimize("",on) */
#endif

NODETYPES nodetype(NODE *nd) {
    if (nd == NIL) return (PNIL);
    return(nd->node_type);
}

static void check_oldyoung(NODE *old, NODE *new) {
    if (VALID_PTR(new) && (new->gc.my_gen < old->gc.my_gen) &&
			      0 == old->gc.oldyoung) {
        add_oldyoung(old);
    }
}

void check_valid_oldyoung(NODE *old, NODE *new) {
    if (new == NIL) return;
    if ((new->gc.my_gen < old->gc.my_gen) && 0 == old->gc.oldyoung) {
        add_oldyoung(old);
    }
}

static void clean_oldyoungs(void) {
    struct oldyoung *current;
    int i;
    NODE *ptr;
#ifdef GC_DEBUG
    FIXNUM num_cleaned = 0;
#endif

    if (FALSE == oldyoungs_dirty) return;

    oldyoung_free = NULL;
    for (current = oldyoung_list; current; current = current->next) {
        for (i = 0; i < current->num_nodes; ) {
            ptr = current->nodes[i];
            if (NTFREE == nodetype(ptr)) {
#ifdef GC_DEBUG
                num_cleaned++;
#endif
                if (NULL == oldyoung_free)
                    oldyoung_free = current;
                current->nodes[i] = current->nodes[--(current->num_nodes)];
                continue;
            }
            i++;
        }
    }

    oldyoungs_dirty = FALSE;

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "oldyoungs %ld + ", num_cleaned); fflush(DEBUGSTREAM);
#endif

}

/* setcar/cdr/object should be called only when the new pointee is really
 * a node.  Otherwise just directly assign to the field (e.g. for CONTs). */

void setobject(NODE *nd, NODE *newobj) {
    nd->n_obj = newobj;
    check_valid_oldyoung(nd, newobj);
}

void setcar(NODE *nd, NODE *newcar) {
    nd->n_car = newcar;
    check_valid_oldyoung(nd, newcar);
}

void setcdr(NODE *nd, NODE *newcdr) {
    nd->n_cdr = newcdr;
    check_valid_oldyoung(nd, newcdr);
}

#ifdef THINK_C
#pragma options(honor_register)
#endif
#ifdef WIN32
#pragma optimize("",off)
#endif



static void do_gc(BOOLEAN full) {
    jmp_buf env;
    setjmp(env);

#ifdef MEM_STATS
    if (full) num_gc_full++;
    else num_gc_incr++;
#endif

    int_during_gc = 0;
    inside_gc++;
    gc(full);
    inside_gc = 0;
    if (int_during_gc != 0) {
	delayed_int();
    }
}

NODE *newnode_unsafe(NODETYPES type) {
    register NODE *newnd;
    static NODE phony;

#ifdef MEM_STATS
    num_newnode++;
#endif

    while ((newnd = free_list) == NIL && NOT_THROWING) {
	do_gc(FALSE);
    }
    if (newnd != NIL) {
	free_list = newnd->nunion.next_free;

        // *((__UINT64_TYPE__ *)newnd) = 0;
	newnd->gc.my_gen = 0;
	newnd->mark_gc = 0;
	newnd->gc.oldyoung = 0;

	newnd->gc.gen_age = gc_age_threshold;
	newnd->next_gen = generation[0];
	generation[0] = zipPTR(newnd);
	settype(newnd, type);
	mem_nodes++;
	if (mem_nodes > mem_max) mem_max = mem_nodes;
	return(newnd);
    } else return &phony;
}

NODE *newnode(NODETYPES type) {
    NODE *newnd = newnode_unsafe(type);

    newnd->n_car = NIL;
    newnd->n_cdr = NIL;
    newnd->n_obj = NIL;

    return newnd;
}

#ifdef THINK_C
#pragma options(!honor_register)
#endif
#ifdef WIN32
/* #pragma optimize("",on) */
#endif

NODE *cons(NODE *x, NODE *y) {
    NODE *val = newnode_unsafe(CONS);

    /* New node can't possibly point to younger one, so no need to check */
    val->n_car = x;
    val->n_cdr = y;
    val->n_obj = NIL;
    return(val);
}

#define mmark(child) {if ((child)->gc.my_gen < nd->gc.my_gen) \
			 {mark(child); got_young = 1;}}

static int inter_gen_mark (NODE *nd) {
/* Mark/traverse pointers to younger generations only */
    NODE** array_ptr;
    NODE* tmp_node;
    int loop;
    int got_young = 0;

    if (nd->gc.my_gen <= mark_gen_gc) return 1;
    switch (nodetype(nd)) {
	case CONS:
	case CASEOBJ:
	case RUN_PARSE:
	case QUOTE:
	case COLON:
	case TREE:
	case LINE:
	case LOCALSAVE:
#ifdef OBJECTS
	case OBJECT:
	case METHOD:
#endif
	    if (VALID_PTR(nd->n_car))
		mmark(nd->n_car);
	    if (VALID_PTR(nd->n_obj))
		mmark(nd->n_obj);
	case CONT:
	    if (VALID_PTR(nd->n_cdr))
		mmark(nd->n_cdr);
	    break;
	case STACK:
	    if (VALID_PTR(nd->n_cdr))
		mmark(nd->n_cdr);
	    array_ptr = (NODE **)car(nd);
	    loop = num_saved_nodes;
	    while (--loop >= 0) {
		tmp_node = *array_ptr++;
		if (VALID_PTR(tmp_node))
		    mmark(tmp_node);
	    }
	    break;
	case ARRAY:
	    array_ptr = getarrptr(nd);
	    loop = getarrdim(nd);
	    while (--loop >= 0) {
		tmp_node = *array_ptr++;
		if (VALID_PTR(tmp_node))
		    mmark(tmp_node);
	    }
	    break;
    }
    /* when got_young = 0, nd no longer points to younger */
    return got_young; 
}

static void gc_inc () {
    NODE **new_gcstack;
    long int loop;

    if (gc_overflow_flag == 1) return;

    if (gctop == &mark_gcstack[gc_stack_size-1])
	gctop = mark_gcstack;
    else
	gctop++;
    if (gctop == gcbottom) { /* gc STACK overflow */
#ifdef GC_DEBUG
	fprintf(DEBUGSTREAM,"\nAllocating new GC stack\n"); fflush(DEBUGSTREAM);
#endif
	if ((new_gcstack = (NODE**) malloc ((size_t) sizeof(NODE *) *
				(gc_stack_size + GCMAX))) == NULL) {

	    /* no room to increse GC Stack */
	    ndprintf(stdout, "\n%t\n", message_texts[CANT_GC]);
	    ndprintf(stdout, "%t\n", message_texts[EXIT_NOW]);

	    gc_overflow_flag = 1;
	} else {
	    /* transfer old stack to new stack */
	    new_gcstack[0] = *gcbottom;
	    if (gcbottom == &mark_gcstack[gc_stack_size-1])
		gcbottom = mark_gcstack;
	    else
		gcbottom++;

	    for (loop = 1 ; gcbottom != gctop ; loop++) {
		new_gcstack[loop] = *gcbottom;
		if (gcbottom == &mark_gcstack[gc_stack_size-1])
		    gcbottom = mark_gcstack;
		else
		    gcbottom++;
	    }
	    gc_stack_size = gc_stack_size + GCMAX;
	    if (gc_stack_malloced == 1) free(mark_gcstack);
	    gc_stack_malloced = 1;

	    mark_gcstack = new_gcstack;
	    gctop = &mark_gcstack[loop];
	    gcbottom = mark_gcstack;
	}
    }
}

/* Iterative mark procedure */
static void mark(NODE* nd) {
    int loop;
    NODE** array_ptr;

    if (gc_overflow_flag == 1) return;
    if (!VALID_PTR(nd)) return; /* NIL pointer */
    if (nd->gc.my_gen > mark_gen_gc) return; /* I'm too old */
    if (nd->mark_gc == current_gc) return; /* I'm already marked */

    *gctop = nd;
    gc_inc();

    while (gcbottom != gctop) {
	nd = *gcbottom;
	if ((VALID_PTR(nd)) && (nd->gc.my_gen <= mark_gen_gc) &&
		(nd->mark_gc != current_gc)) {
	    if (nd->mark_gc == GC_GCTWA) {
		nd->mark_gc = GC_NOTMARKED; /* this is a caseobj during gctwa */
		goto no_mark;	    /* so don't really mark yet */
	    }
	    nd->mark_gc = current_gc;
#ifdef GC_DEBUG
	    num_examined++;
#endif
	    switch (nodetype(nd)) {
		case CONS:
		case CASEOBJ:
		case RUN_PARSE:
		case QUOTE:
		case COLON:
		case TREE:
		case LINE:
		case LOCALSAVE:
#ifdef OBJECTS
		case OBJECT:
		case METHOD:
#endif
		    *gctop = nd->n_car;
		    gc_inc();
		    *gctop = nd->n_obj;
		    gc_inc();
		case CONT:
		    *gctop = nd->n_cdr;
		    gc_inc();
		    break;
		case STACK:
		    *gctop = nd->n_cdr;
		    gc_inc();
		    array_ptr = (NODE **)car(nd);
		    loop = num_saved_nodes;
		    while (--loop >= 0) {
			*gctop = *array_ptr++;
			gc_inc();
		    }
		    break;
		case ARRAY:
		    array_ptr = getarrptr(nd);
		    loop = getarrdim(nd);
		    while (--loop >= 0) {
			*gctop = *array_ptr++;
			gc_inc();
		    }
		break;
	    }
	}
no_mark:
	if (gcbottom == &mark_gcstack[gc_stack_size-1])
	    gcbottom = mark_gcstack;
	else
	    gcbottom++;
    }
}

static void gc(BOOLEAN no_error) {
    NODE *top;
    NODE **top_stack;
    NODE *nd, *tmpnd;
    long int num_freed = 0;
    NODE **tmp_ptr;
    ZPTRTYPE *tmp_zptr;
    long int freed_sofar = 0;
    NODE** array_ptr;
    NODE* tmp_node;
    NODE *obj, *caselist;
    int anygood;
    int i, j;
    short int loop;
    int gen_gc; /* deepest generation to garbage collect */
    int gctwa;	/* garbage collect truly worthless atoms */
    struct oldyoung *oldies;

    if (gc_overflow_flag == 1) {
	if (!addseg()) {
	    err_logo(OUT_OF_MEM, NIL);
	    if (free_list == NIL)
		err_logo(OUT_OF_MEM_UNREC, NIL);
	}
	return;
    }

    if (check_throwing)
        return;

    top_stack = &top;

    mark_gen_gc = gen_gc = (no_error ? max_gen : next_gen_gc);

    gctwa = (gen_gc == max_gen && max_gen > 1) || no_error;

    if (gctwa) {
	/* Every caseobj must be marked twice to count */
	for (loop = 0; loop < HASH_LEN ; loop++) {
	    for (nd = hash_table[loop]; nd != NIL; nd = cdr(nd)) {
		tmpnd = caselist__object(car(nd));
		while (tmpnd != NIL) {
		    (car(tmpnd))->mark_gc = GC_GCTWA;
		    tmpnd = cdr(tmpnd);
		}
	    }
	}
    }

re_mark:

    /* wrap around current_gc: GC_NOTMARKED 1 ... GC_GCTWA */
    if (++current_gc == GC_GCTWA) {
        clear_mark_gc();
        current_gc = 1;
    }

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "gen = %d\n", gen_gc); fflush(DEBUGSTREAM);
    num_examined = 0;
#endif

    /* Begin Mark Phase */

    /* Check globals for NODE pointers */

    mark(current_line);
    mark(command_line);    //
    mark(deepend_proc_name);

    mark(Listvalue);
    mark(Dotsvalue);
    mark(Unbound);
    mark(Not_Enough_Node);

    mark(cnt_list);
    mark(cnt_last);
    mark(throw_node);
    mark(err_mesg);
    mark(var_stack);
    mark(output_node);
    mark(output_unode);
    mark(last_call);
    mark(Regs_Node);
    mark(eval_buttonact);
    mark(file_list);
    mark(reader_name);
    mark(writer_name);
    mark(file_prefix);
    mark(save_name);
    mark(the_generation);
    mark(tree_dk_how);
#ifdef OBJECTS
    mark(logo_object);
    mark(current_object);
    mark(askexist);
#endif

    mark(stack);
    mark(numstack);
    mark(expresn);
    mark(val);
    mark(parm);
    mark(catch_tag);
    mark(arg);

    mark(proc);
    mark(argl);
    mark(unev);
    mark(fun);
    mark(ufun);
    mark(var);
    mark(vsp);
    mark(qm_list);
    mark(formals);
    mark(last_ufun);
    mark(this_line);
    mark(last_line);
    mark(current_unode);
    mark(didnt_output_name);
    mark(didnt_get_output);
#ifdef OBJECTS
    mark(usual_parent);
    mark(usual_caller);
#endif


#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "globals %ld + ", num_examined); fflush(DEBUGSTREAM);
    num_examined = 0;
#endif

    for (loop = 0; loop < HASH_LEN ; loop++)
	mark(hash_table[loop]);

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "oblist %ld + ", num_examined); fflush(DEBUGSTREAM);
    num_examined = 0;
#endif

    /* Check Stack for NODE pointers */

    if (top_stack < bottom_stack) { /* check direction stack grows */
	for (tmp_ptr = top_stack; tmp_ptr <= bottom_stack; 
#if defined(THINK_C) || defined(__RZTC__) || defined(GC_TWOBYTE)
	     tmp_ptr = (NODE **)(((unsigned long int)tmp_ptr)+2)
#else
	     tmp_ptr++
#endif
	     ) {
		if (valid_pointer(*tmp_ptr)) {
		    mark(*tmp_ptr);
		}
	}
    } else {
	for (tmp_ptr = top_stack; tmp_ptr >= bottom_stack; 
#if defined(THINK_C) || defined(__RZTC__) || defined(GC_TWOBYTE)
	     tmp_ptr = (NODE **)(((unsigned long int)tmp_ptr)-2)
#else
	     tmp_ptr--
#endif
	     ) {
		if (valid_pointer(*tmp_ptr)) {
		    mark(*tmp_ptr);
		}
	}
    }

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "stack %ld + ", num_examined); fflush(DEBUGSTREAM);
    num_examined = 0;
    num_visited = 0;
#endif

    /* check pointers from old generations to young */
    for (oldies = oldyoung_list; oldies; oldies = oldies->next) {
        for (i = 0; i < oldies->num_nodes; ) {
            tmp_node = oldies->nodes[i];
            j = inter_gen_mark(tmp_node);
            if (0 == j) {
                tmp_node->gc.oldyoung = 0;
                oldies->nodes[i] = oldies->nodes[--(oldies->num_nodes)];
                continue;
            }
            i++;
#ifdef GC_DEBUG
            num_visited++;
#endif
        }
    }

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "inter_gen %ld marked %ld visited\n", num_examined, num_visited); fflush(DEBUGSTREAM);
    num_examined = 0;
#endif

    if (gc_overflow_flag) return;

    if (gctwa) {

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "GCTWA: "); fflush(DEBUGSTREAM);
    num_examined = 0;
#endif
	for (loop = 0; loop < HASH_LEN ; loop++) {
	    tmpnd = NIL;
	    for (nd = hash_table[loop]; nd != NIL; nd = cdr(nd)) {
		obj = car(nd);
		if (procnode__object(obj) == UNDEFINED &&
		    valnode__object(obj) == UNBOUND &&
		    plist__object(obj) == NIL &&
		    !flag__object(obj, PERMANENT)) {
#ifdef GC_DEBUG
			    num_examined++;
#endif
			anygood = 0;
			for (caselist = caselist__object(obj);
					caselist != NIL; caselist = cdr(caselist)) {
			    if ((car(caselist))->mark_gc == current_gc) {
				anygood = 1;
				break;
			    }
			}
			if (anygood) {	/* someone points here, don't gctwa */
			    tmpnd = nd;
			} else {	/* do gctwa */
			    if (tmpnd == NIL)
				hash_table[loop] = cdr(hash_table[loop]);
			    else
				setcdr(tmpnd, cdr(nd));
			}
		} else			/* has a value, don't gctwa */
		    tmpnd = nd;
	    }
	}

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "%ld collected\n", num_examined); fflush(DEBUGSTREAM);
    num_examined = 0;
#endif
	gctwa = 0;
	goto re_mark;
    }

    /* Begin Sweep Phase */
   	
    for (loop = gen_gc; loop >= 0; loop--) {
	tmp_zptr = &generation[loop];
	for (nd = unzipPTR(generation[loop]);
             nd != NIL;
             nd = unzipPTR(*tmp_zptr))
        {
	    if (nd->mark_gc == current_gc) {
		if (--(nd->gc.gen_age) == 0 && loop < NUM_GENS-1) {
		    /* promote to next gen */
		    *tmp_zptr = nd->next_gen;
		    nd->next_gen = generation[loop+1];
		    generation[loop+1] = zipPTR(nd);
		    nd->gc.my_gen = loop+1;
		    if (max_gen == loop) max_gen++;
		    nd->gc.gen_age = gc_age_threshold;
		    switch (nodetype(nd)) {
			case CONS:
			case CASEOBJ:
			case RUN_PARSE:
			case QUOTE:
			case COLON:
			case TREE:
			case LINE:
			case LOCALSAVE:
#ifdef OBJECTS
			case OBJECT:
			case METHOD:
#endif
                            clean_oldyoungs();
			    check_oldyoung(nd, nd->n_car);
			    check_oldyoung(nd, nd->n_obj);
			case CONT:
                            clean_oldyoungs();
			    check_oldyoung(nd, nd->n_cdr);
			    break;
			case STACK:
                            clean_oldyoungs();
			    check_oldyoung(nd, nd->n_cdr);
			    array_ptr = (NODE **)car(nd);
			    i = num_saved_nodes;
			    while (--i >= 0) {
				tmp_node = *array_ptr++;
				check_oldyoung(nd, tmp_node);
			    }
			    break;
			case ARRAY:
                            clean_oldyoungs();
			    array_ptr = getarrptr(nd);
			    i = getarrdim(nd);
			    while (--i >= 0) {
				tmp_node = *array_ptr++;
				check_oldyoung(nd, tmp_node);
			    }
			    break;
		    }
       		} else {
		    /* keep in this gen */
		    tmp_zptr = &(nd->next_gen);
         	}
	    } else {
		/* free */
		num_freed++;
		mem_nodes--;
         	*tmp_zptr = nd->next_gen;
     		if (nd->gc.oldyoung) {
                    oldyoungs_dirty = TRUE;
		}
        	switch (nodetype(nd)) {
		    case ARRAY:
			free((char *)getarrptr(nd));
             		break;
		    case STACK:
			free((char *)car(nd));
			break;
		    case STRING:
		    case BACKSLASH_STRING:
		    case VBAR_STRING:
			if (getstrhead(nd) != NULL &&
				    decstrrefcnt(getstrhead(nd)) == 0)
			    free(getstrhead(nd));
			break;
		}
		settype (nd, NTFREE);
	 	nd->nunion.next_free = free_list;
	 	free_list = nd;
	    }
	}
        clean_oldyoungs();
#ifdef GC_DEBUG
	fprintf(DEBUGSTREAM, "%ld + ", num_freed - freed_sofar); fflush(DEBUGSTREAM);
#endif
	freed_sofar = num_freed;
    }

#ifdef GC_DEBUG
    fprintf(DEBUGSTREAM, "= %ld freed\n", num_freed); fflush(DEBUGSTREAM);
#endif

    if (num_freed > freed_threshold)
	next_gen_gc = 0;
    else if (gen_gc < max_gen)
	next_gen_gc = gen_gc+1;
    else
	next_gen_gc = 0;

    if (num_freed < freed_threshold) {
	if (!addseg() && num_freed < 50 && gen_gc == max_gen && !no_error) {
	    err_logo(OUT_OF_MEM, NIL);
	    if (free_list == NIL)
		err_logo(OUT_OF_MEM_UNREC, NIL);
	}
#ifdef __RZTC__
	(void)addseg();
#endif
    }

#ifdef GC_DEBUG
/*    getchar(); */
#endif
}

#ifdef GC_DEBUG
void prname(NODE *foo) {
    fprintf(DEBUGSTREAM, "%s ", (char*) car(foo)); fflush(DEBUGSTREAM);
}
#endif

NODE *lgc(NODE *args) {
    do_gc(args != NIL);
    return UNBOUND;
}

NODE *lnodes(NODE *args) {
    long int temp_max, temp_nodes;

#ifdef GC_DEBUG
/*    map_oblist(&prname); */
#endif
    do_gc(TRUE);	/* get real in-use figures */
    temp_max = mem_max;
    temp_nodes = mem_nodes;
    mem_max = mem_nodes;
    return cons(make_intnode(temp_nodes),
		cons(make_intnode(temp_max), NIL));
}

void fill_reserve_tank(void) {
    NODE *newnd, *p = NIL;
    int i = 50;

    while (--i >= 0) {	/* make pairs not in any generation */
	if ((newnd = free_list) == NIL) break;
	free_list = newnd->nunion.next_free;
	settype(newnd, CONS);
	newnd->n_car = NIL;
	newnd->n_cdr = p;
	newnd->n_obj = NIL;
	newnd->next_gen = 0;
	newnd->gc.oldyoung = 0;
	p = newnd;
    }
    reserve_tank = p;
}

void use_reserve_tank(void) {
    NODE *nd = reserve_tank;
	
    reserve_tank = NIL;
    for ( ; nd != NIL; nd = cdr(nd) ) {
    	settype(nd, NTFREE);
    	nd->nunion.next_free = free_list;
    	free_list = nd;
    }
}

void check_reserve_tank(void) {
    if (reserve_tank == NIL) fill_reserve_tank();
}

void mem_init(void) {
    char *p0, *p1;
    (void)addseg();
    oldyoung_list = addoldyoungseg();
    oldyoung_free = oldyoung_list;
    p0 = (char*)&(segment_list->nodes[0]);
    p1 = (char*)&(segment_list->nodes[1]);
    // fprintf(stderr,"node ptr diff=%ld\n",p1-p0);
}

void mem_stat(void) {
#ifdef MEM_STATS
    fprintf(stderr,"#oldyoung_segments = %d\n",num_oldyoung_segments);
    fprintf(stderr,"#segments = %d\n",num_segment_bases);
    fprintf(stderr,"#newnode  = %d\n",num_newnode);
    fprintf(stderr,"#incr GC = %d\n",num_gc_incr);
    fprintf(stderr,"#full GC = %d\n",num_gc_full);
#endif
    return;
}
