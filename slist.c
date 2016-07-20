 #include <stdlib.h>
#include <stdio.h>
#include "slist.h"

void slist_init(slist_t *slist) {
    if (!slist) {
        slist_t *slistTemp = (slist_t*) malloc(sizeof(slist_t));
        slist = slistTemp;
    }

    slist_head(slist) = NULL;
    slist_tail(slist) = NULL;
    slist_size(slist) = 0;
}

void slist_destroy(slist_t *slist,slist_destroy_t destroyFlag) {
    if (!slist)
    return;

    if (slist_size(slist) > (unsigned int) 0) {
        slist_node_t *head_tmp = slist_head(slist), *node_tmp;
        unsigned int i = 0;
        while (i < slist_size(slist)) {
            if (destroyFlag == SLIST_FREE_DATA)
            free (slist_data(head_tmp));

            node_tmp = head_tmp;
            head_tmp = slist_next(head_tmp);
            free (node_tmp);

            i++;
        }
    }

    slist_head(slist) = NULL;
    slist_tail(slist) = NULL;
    free(slist);
    slist = NULL;
}

void *slist_pop_first(slist_t *slist) {
    if (!slist)
    return NULL;

    if (slist_size(slist) ==0)
    return NULL;

    void *pData = slist_data(slist_head(slist));
    slist_node_t *node_tmp = slist_head(slist);
    slist_head(slist) = slist_next(slist_head(slist));
    free(node_tmp);
    
    slist_size(slist) -= 1;

    if(slist_size(slist) == 0) {
        slist_head(slist) = NULL;
        slist_tail(slist) = NULL;
    }

    return pData;
}

int slist_append(slist_t *slist,void *data) {
    if (!slist)
    return -1;

    if (!data)
    return 0;

    slist_node_t *newNode = (slist_node_t*) malloc(sizeof(slist_node_t));
    if (!newNode) {
        perror ("cannot allocate memory in: slist_append");
        return -1;
    }

    slist_data(newNode) = data;
    if (slist_size(slist) == 0) {
        slist_head(slist) = newNode;
        slist_tail(slist) = newNode;
    }
    else {
        slist_next(slist_tail(slist)) = newNode;
        slist_tail(slist) = newNode;
    }

    slist_size(slist) += 1;

    return 0;
}

int slist_prepend(slist_t *slist,void *data) {
    if (!slist)
    return -1;

    if (!data)
    return 0;

    slist_node_t *newNode = (slist_node_t*) malloc(sizeof(slist_node_t));
    if (!newNode) {
        perror ("cannot allocate memory in: slist_prepend");
        return -1;
    }

    slist_data(newNode) = data;
    if (slist_size(slist) == 0) {
        slist_head(slist) = newNode;
        slist_tail(slist) = newNode;
    }
    else {
        slist_next(newNode) = slist_head(slist);
        slist_head(slist) = newNode;
    }

    slist_size(slist) += 1;

    return 0;
}

int slist_append_list(slist_t* slistDest, slist_t* slistSrc) {
    if (!slistDest)
    return -1;

    if (!slistSrc)
    return 0;

    slist_node_t *headSrc = slist_head(slistSrc);
    while (headSrc) {
        if (slist_append (slistDest, slist_data(headSrc)) == -1) {
            printf("cannot append data in: slist_append_list");
            return -1;
        }

        headSrc = slist_next(headSrc);
    }

    slist_destroy(slistSrc, SLIST_LEAVE_DATA);

    return 0;
}
