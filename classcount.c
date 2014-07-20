#include <stdio.h>
#include <stdlib.h>
void increment(int);
void printresults(size_t);
static size_t c4 = 0;
static size_t c5 = 0;
static size_t c6 = 0;
static size_t c7 = 0;
static size_t c8 = 0;
static size_t c9 = 0;
static size_t c10 = 0;
static size_t c11 = 0;
static size_t c12 = 0;
static size_t c13 = 0;
static size_t c14 = 0;
static size_t c15 = 0;
static size_t cn = 0;
int main(){
    FILE *f;
    int class;
    size_t c;
    f = fopen("./c.txt", "r");
    c = 0;
    while(EOF != fscanf(f,"%d",&class)){
        increment(class);
    }
    fclose(f);
    printresults(c);
}

void printresults(size_t c){
    printf("SIZE4:%d\t", c4);
    printf("SIZE5:%d\t", c5);
    printf("SIZE6:%d\t", c6);
    printf("SIZE7:%d\t", c7);
    printf("SIZE8:%d\t", c8);
    printf("SIZE9:%d\t", c9);
    printf("SIZE10:%d\t", c10);
    printf("SIZE11:%d\t", c11);
    printf("SIZE12:%d\t", c12);
    printf("SIZE13:%d\t", c13);
    printf("SIZE14:%d\t", c14);
    printf("SIZE15:%d\t", c15);
    printf("SIZEN:%d\t\n", cn);
    printf("total allocations: %zd\n",c);
}

void increment(int n){
    switch(n){
    case 0:
        c4++;
        break;
    case 1:
        c5++;
        break;
    case 2:
        c6++;
        break;
    case 3:
        c7++;
        break;
    case 4:
        c8++;
        break;
    case 5:
        c9++;
        break;
    case 6:
        c10++;
        break;
    case 7:
        c11++;
        break;
    case 8:
        c12++;
        break;
    case 9:
        c13++;
        break;
    case 10:
        c14++;
        break;
    case 11:
        c15++;
        break;
    case 12:
        cn++;
        break;
    }
}
