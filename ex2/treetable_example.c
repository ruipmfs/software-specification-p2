#include <stdio.h>
#include "treetable.h"

int main() {
    TreeTable *table;
    treetable_new(&table);

    int key1 = 1;
    int key2 = 2;

    char value1[] = "aaa"; 
    char value2[] = "bbb";

    treetable_add(table, &key1, value1);
    treetable_add(table, &key2, value2);

    if (treetable_contains_key(table, &key1)){

        void* value;
        treetable_get(table, &key1, &value);
        
        printf("Treetable contains pair => (%d:%s)\n", key1, (char*) value);
    }
    treetable_destroy(table);
}
