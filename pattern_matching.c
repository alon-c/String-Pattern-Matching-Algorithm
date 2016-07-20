 #include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "pattern_matching.h"

/* Initializes the fsm parameters (the fsm itself sould be allocated).  Returns 0 on success, -1 on failure.
*  this function should init zero state
*/
int pm_init(pm_t *pm) {
    if (!pm) {
        pm_t *pm_tmp = (pm_t*) malloc(sizeof(pm_t));
        if (!pm_tmp) {
            perror ("cannot allocate memory for: pm, in: pm_init");
            return -1;
        }

        pm= pm_tmp;
    }

    /* pm initialization */

    pm_state_t *zerostate_tmp = (pm_state_t*) malloc(sizeof(pm_state_t));
    if (!zerostate_tmp) {
        perror ("cannot allocate memory for: zerostate in: pm_init");
        return -1;
    }

    slist_t *output_tmp = (slist_t*) malloc(sizeof(slist_t));
    if (!output_tmp) {
        perror ("cannot allocate memory for: output in: pm_init");
        return -1;
    }

    slist_t *_transitions_tmp = (slist_t*) malloc(sizeof(slist_t));
    if (!_transitions_tmp) {
        perror ("cannot allocate memory for: _transitions in: pm_init");
        return -1;
    }

    slist_init(output_tmp);

    slist_init(_transitions_tmp);

    zerostate_tmp->id = 0;
    zerostate_tmp->depth = 0;
    zerostate_tmp->output = output_tmp;
    zerostate_tmp->fail = NULL;
    zerostate_tmp->_transitions = _transitions_tmp;

    pm->newstate = 0;
    pm->zerostate = zerostate_tmp;

    return 0;
}



/* Adds a new string to the fsm, given that the string is of length n.
Returns 0 on success, -1 on failure.*/
int pm_addstring(pm_t *pm,unsigned char *pattern, size_t n) {
    if ((!pm) || (!pattern))
    return -1;

    pm_state_t *state = pm->zerostate;
    int i = 0;
    while ((pm_goto_get(state, pattern[i]) != NULL) && (i < n)) {
        state = pm_goto_get(state, pattern[i]);
        i++;
    }

    if(i == n)
    return 0;

    int j = i;
    for (j = i; j < n; j++) {
        //preparing to create new state, incramenting pm newstate counter
        pm->newstate += 1;

        //print new state message
        printf ("Allocating state %drn", pm->newstate);

        pm_state_t *newstate_tmp = (pm_state_t*) malloc(sizeof(pm_state_t));
        if (!newstate_tmp) {
            perror ("cannot allocate memory for: newstate in: pm_addstring");
            return -1;
        }

        slist_t *output_tmp = (slist_t*) malloc(sizeof(slist_t));
        if (!output_tmp) {
            perror("cannot allocate memory for: newstate.output in: pm_addstring");
            return -1;
        }

        slist_t *_transitions_tmp = (slist_t*) malloc(sizeof(slist_t));
        if (!_transitions_tmp) {
            perror ("cannot allocate memory for: newstate._transitions in: pm_addstring");
            return -1;
        }

        slist_init(output_tmp);

        slist_init(_transitions_tmp);

        /* pm update, newstate initialization */
        newstate_tmp->id = pm->newstate;
        newstate_tmp->depth = j;
        newstate_tmp->output = output_tmp;
        newstate_tmp->fail = NULL;
        newstate_tmp->_transitions = _transitions_tmp;

        // print edge creation message
        printf ("%d -> %c -> %drn", state->id, pattern[j], newstate_tmp->id);

        if (pm_goto_set(state, pattern[j], newstate_tmp) == -1) {
            fprintf (stderr, "cannot set tranzition arrow in: pm_addstring");
            return -1;
        }

        state = pm_goto_get(state, pattern[j]);
    }

    /* set output pattern for reciveing state */
    unsigned char *pPattern = (unsigned char*) malloc (sizeof(unsigned char) * (strlen(pattern) +1));
    if (!pPattern)
    return -1;

    strcpy(pPattern, pattern);

    slist_t *pOutput = state->output;
    if (slist_append(pOutput, pPattern) == -1) {
        fprintf (stderr, "cannot append to reciveing state data for the output, in: pm_addstring");
        return -1;
    }

    return 0;
}

/* Finalizes construction by setting up the failrue transitions, as
well as the goto transitions of the zerostate.
Returns 0 on success, -1 on failure.*/
int pm_makeFSM(pm_t *pm) {
    if (!pm)
    return -1;

    slist_t *q = (slist_t*) malloc(sizeof(slist_t));
    if (!q)
    return -1;

    slist_init(q);

    pm_state_t *state = pm->zerostate;
    slist_node_t *pHead = slist_head(state->_transitions);
    unsigned int k = 0;
    while (k < slist_size(state->_transitions)) {
        if (slist_append(q, ((pm_labeled_edge_t*) slist_data(pHead))->state) == -1)
        return -1;

        ((pm_labeled_edge_t*) slist_data(pHead))->state->fail = pm->zerostate;
        pHead = slist_next(pHead);
        k++;
    }

    pm_state_t *pR;
    pm_state_t *pState;
    pm_state_t *pRTranState;
    slist_node_t *pStateOutputHead;

    while (slist_size(q) > ((unsigned int) 0)) {
        pR =(pm_state_t*) slist_pop_first(q);
        if (!pR){
            break;
        }

        if(slist_size(pR->_transitions) == ((unsigned int) 0)) {
            continue;
        }

        slist_node_t *pRHead = slist_head(pR->_transitions);
        unsigned int i = 0;
        while (i < slist_size(pR->_transitions)) {
            pRTranState = ((pm_labeled_edge_t*) slist_data(pRHead))->state;
            if (slist_append(q, pRTranState) == -1)
            return -1;

            pState = pR->fail;
            while (pm_goto_get(pState, ((pm_labeled_edge_t*) slist_data(pRHead))->label) == NULL) {
                if (pState->fail !=NULL)
                pState = pState->fail;
            }

            if (pm_goto_get(pState, ((pm_labeled_edge_t*) slist_data(pRHead))->label) != NULL)
            pState = pm_goto_get(pState, ((pm_labeled_edge_t*) slist_data(pRHead))->label);

            printf ("Setting f(%d) = %drn", pRTranState->id, pState->id);

            pRTranState->fail = pState;

            pStateOutputHead = slist_head(pState->output);
            unsigned char *strTmp = NULL;
            unsigned int j = 0;
            while (j < slist_size(pState->output)) {
                strTmp = (unsigned char*) malloc((strlen(slist_data(pStateOutputHead)) +1) * sizeof(unsigned char));
                strcpy(strTmp, slist_data(pStateOutputHead));
                if (slist_append(pRTranState->output, (unsigned char*) strTmp) == -1)
                return -1;

                pStateOutputHead = slist_next(pStateOutputHead);
                j++;
            }

            pRHead = slist_next(pRHead);
            i++;
        }
    }

    pm->zerostate->fail = pm->zerostate;
    slist_destroy(q, SLIST_LEAVE_DATA);

    return 0;
}

int pm_goto_set(pm_state_t *from_state, unsigned char symbol, pm_state_t *to_state) {
    slist_t *tran = from_state->_transitions;
    pm_labeled_edge_t *edg = (pm_labeled_edge_t*) malloc(sizeof(pm_labeled_edge_t));
    if (!edg)
    return -1;

    edg->label = symbol;
    edg->state = to_state;
    if(slist_append(tran, edg) == -1)
    return -1;

    return 0;
}

pm_state_t* pm_goto_get(pm_state_t *state, unsigned char symbol) {
    slist_t *tran = state->_transitions;
    slist_node_t *head = slist_head(tran);
    pm_labeled_edge_t *edg_tmp;
    unsigned int i = 0;
    while (i < slist_size(tran)) {
        edg_tmp = (pm_labeled_edge_t*) slist_data(head);
        if ((edg_tmp->label) == symbol)
        return edg_tmp->state;

        head = slist_next(head);
        i++;
    }

    return NULL;
}

slist_t* pm_fsm_search(pm_state_t *root,unsigned char *text,size_t n) {
    if ((!root) || (!text))
    return NULL;

    slist_t *res = (slist_t*) malloc(sizeof(slist_t));
    if (!res)
    return NULL;

    slist_init(res);

    pm_state_t *pRoot = root;
    pm_match_t *pMatchNode;
    slist_t *pOutput;
    slist_node_t *pOutputHead;
    unsigned char *pOutputPattern;

    int i = 0;
    while (i < n) {
        while (pm_goto_get(pRoot, text[i]) == NULL) {
            pRoot = pRoot->fail;

            if (pRoot->id == 0)
            break;
        }

        if (pm_goto_get(pRoot, text[i]) == NULL) {
            i++;
            continue;
        }

        pRoot = pm_goto_get(pRoot, text[i]);
        pOutput = pRoot->output;
        pOutputHead = slist_head(pOutput);
        int j;
        for (j = 0; j < slist_size(pOutput); j++) {
            pMatchNode = (pm_match_t*) malloc(sizeof(pm_match_t));
            if (!pMatchNode) {
                exit(-1);
            }

            pOutputPattern = (unsigned char*) slist_data(pOutputHead);
            pMatchNode->pattern = pOutputPattern;
            pMatchNode->start_pos = i - strlen(pOutputPattern) +1;
            pMatchNode->end_pos = i;
            pMatchNode->fstate = pRoot;

            if (slist_append(res, pMatchNode) == -1){
                exit(-1);
            }

            printf("Pattern: %s, start at: %d, ends at: %d, accepting state = %drn", pOutputPattern, (i - ((int)strlen(pOutputPattern)) +1), i, pRoot->id);

            pOutputHead = slist_next(pOutputHead);
        }

        i++;
    }

    return res;
}

void pm_destroy(pm_t *pm) {
    if (!pm)
    return;

    slist_t *q = (slist_t*) malloc(sizeof(slist_t));
    if (!q)
    return;

    slist_init(q);

    pm_state_t *state = pm->zerostate;
    slist_node_t *pHead = slist_head(state->_transitions);
    unsigned int k = 0;
    while (k < slist_size(state->_transitions)) {
        if (slist_append(q, ((pm_labeled_edge_t*) slist_data(pHead))->state) == -1)
        return;

        pHead = slist_next(pHead);
        k++;
    }

    pm_state_t *pR;
    pm_state_t *pRTranState;

    while (slist_size(q) > 0) {
        pR =(pm_state_t*) slist_pop_first(q);

        if (!pR){
            break;
        }

        if(slist_size(pR->_transitions) > ((unsigned int) 0)) {
            slist_node_t *pRHead = slist_head(pR->_transitions);
            unsigned int i = 0;
            while (i < slist_size(pR->_transitions)) {
                pRTranState = ((pm_labeled_edge_t*) slist_data(pRHead))->state;
                if (slist_append(q, pRTranState) == -1)
                return;

                pRHead = slist_next(pRHead);
                i++;
            }
        }

        slist_destroy(pR->output, SLIST_FREE_DATA);
        slist_destroy(pR->_transitions, SLIST_FREE_DATA);
        pR->fail = NULL;
        free (pR);
    }

    slist_destroy(pm->zerostate->output, SLIST_FREE_DATA);
    slist_destroy(pm->zerostate->_transitions, SLIST_FREE_DATA);
    pm->zerostate->fail = NULL;
    free(pm->zerostate);
   
    slist_destroy(q, SLIST_LEAVE_DATA);
   }