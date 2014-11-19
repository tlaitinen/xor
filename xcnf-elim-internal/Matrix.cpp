#include "Matrix.hpp"
#include <malloc.h>
#include <math.h>
#include <string.h>
#include <assert.h>
#include <limits.h>
#include <iostream>
#ifdef DEBUG
#define D(x) { std::cout << x << std::endl; }
#else
#define D(x)
#endif
static unsigned char wordbits[65536];
static int popcount( uint32_t i )
{
        return( wordbits[i&0xFFFF] + wordbits[i>>16] );
}


using namespace std;
const int Matrix::bitsPerElem = sizeof(Elem) * 8;

Matrix::Matrix(int w, int h) : 
    width(w), 
    height(h),
    elemsPerRow(ceil(width / (float) bitsPerElem)),
    elemsPerCol(ceil(height / (float) bitsPerElem)),
    naAlloc(elemsPerRow) {
        D("width " << width << " height " << height);
        D("elemsPerRow " << elemsPerRow);
        D("elemsPerCol " << elemsPerCol);

    rows = (Elem*) malloc(elemsPerRow * height * sizeof(Elem));
    cols = (Elem*) malloc(elemsPerCol * width * sizeof(Elem));
//    nonAssigned = &rows[(height-2)*elemsPerRow];
//    values = &rows[(height-1)*elemsPerRow];
//    nonAssigned = (Elem*) malloc(elemsPerRow * sizeof(Elem));
    nonAssigned = naAlloc.alloc();
    values = (Elem*) malloc(elemsPerRow * sizeof(Elem));
    naCount = (int*) malloc(sizeof(int) * height);

    memset(rows, 0, sizeof(Elem)*elemsPerRow * height);
    memset(cols, 0, sizeof(Elem)*elemsPerCol * width);
    memset(nonAssigned, 255, sizeof(Elem)*elemsPerRow);
    memset(values, 0, sizeof(Elem)*elemsPerRow);
    memset(naCount, 0, sizeof(int)*height);
    if (wordbits[1] != 1) {
        for (size_t i =0 ; i < 65536; i++) {
            wordbits[i] = __builtin_popcount(i);
        }
    }
}
Matrix::~Matrix() {
    free(rows);
    free(cols);
//    free(nonAssigned);
    free(values);
    free(naCount);
 /*   for (size_t i = 0; i < nonAssignedCopies.size(); i++) {
        free(nonAssignedCopies[i]);
    }
   */             
}

void Matrix::set(int x, int y, int value) {

    assert(x >= 0 && y >= 0);
    assert(x < width && y < height);
    Elem* rp = &rows[y*elemsPerRow];
    Elem* cp = &cols[x*elemsPerCol];
    Elem* nap = nonAssigned;
    nap += x / bitsPerElem;
    rp += x / bitsPerElem;
    cp += y / bitsPerElem;
    Elem rm = 1 << (x % bitsPerElem);
    Elem cm = 1 << (y % bitsPerElem);
    

    if (value) {
        if ((*rp & rm) == 0) {
            *rp |= rm;
            *cp |= cm;
            if (*nap & rm) {
                naCount[y]++;
            }            
        }
    } else {
        if (*rp & rm ) {

            *rp &= ~rm;
            *cp &= ~cm;
            if (*nap & rm) {
                naCount[y]--;
            }
        }
    }    
    assert(((*rp & rm) != 0) == ((*cp & cm) != 0));
#ifdef DEBUG
    rp = &rows[y*elemsPerRow];
    nap = nonAssigned;
    int nonAss = 0;
    for (int count = elemsPerRow; count > 0; count--) {
        if ( *rp) {
            Elem na = *nap & *rp;
            nonAss += popcount(na);
        }
        nap++;
        rp++;
    }
    assert(nonAss == naCount[y]);

#endif

}
int Matrix::get(int x, int y) const {
    assert(x >= 0 && y >= 0);
    assert(x < width && y < height);
    const Elem* rp = &rows[y*elemsPerRow];
    const Elem* cp = &cols[x*elemsPerCol];
    rp += x / bitsPerElem;
    cp += y / bitsPerElem;
    Elem shl = x % bitsPerElem;
    Elem rm = 1 << shl;
    shl = y % bitsPerElem;
    Elem cm = 1 << shl;

    assert(((*rp & rm) != 0) == ((*cp & cm) != 0));
    if (*rp & rm)
        return 1;
    return 0;
}
void Matrix::getRow(int y, std::vector<int>& row) {
    assert(y >= 0 && y < height);

    Elem* rp = &rows[y * elemsPerRow];
    int base = 0;
    row.clear();
    for (int count = elemsPerRow; count > 0; count--) {
        if (*rp) {
            Elem tmp = *rp;
            while(tmp) {
                int p = __builtin_ctz(tmp);
                Elem m = 1 << p;
                tmp &= ~m;
                row.push_back(base + p);
            }
        }
        base += bitsPerElem;
        rp++;
    }

}
void Matrix::getCol(int x, std::vector<int>& col) {
    assert(x >= 0 && x < width);

    Elem* cp = &cols[x * elemsPerCol];
    int base = 0;
    col.clear();
    Elem* endCp = &cols[(x+1) * elemsPerCol];
    for (; cp != endCp; cp++) {
        D("in getCol!");
        if (*cp) {
            D("non-zero");
            Elem tmp = *cp;
            while(tmp) {
                int p = __builtin_ctz(tmp);
                Elem m = 1 << p;
                tmp &= ~m;
                col.push_back(base + p);
                D("yippii!");
                assert(col.back() < height);
            }
        }
        base += bitsPerElem;
    }
}

void Matrix::getAssigned(int y, std::vector<int>& row) {

    assert(y >= 0 && y < height);

    Elem* rp = &rows[y * elemsPerRow];
    Elem* vp = values;
    Elem* nap = nonAssigned;
    Elem* endNap = nonAssigned + elemsPerRow;
    int base = 0;
    for (; nap != endNap; nap++) {
        if (*rp) {
            Elem tmp = *rp & ~*nap;
            while(tmp) {
                int p = __builtin_ctz(tmp);
                Elem m = 1 << p;
                tmp &= ~m;
                int v = (elemsPerRow - (int)(endNap - nap))*bitsPerElem +p;
                if (v != 0) {
                    row.push_back((*vp & m) ? -v : v);
                }
            }
        }
        rp++;
        vp++;
    }
}

int Matrix::addRow(int src, int dst) {
    assert(src >= 0 && src < height);
    assert(dst >= 0 && dst < height);


    Elem* srcRp = &rows[src*elemsPerRow];
    Elem* dstRp = &rows[dst*elemsPerRow];
    Elem* cp = cols + dst / bitsPerElem;
    Elem* nap = nonAssigned;
    Elem* vp = values;
    int nonAss = 0;
    int implied = 0;
    Elem parity = 0;
    Elem cm = 1 << (dst % bitsPerElem); 
    Elem* endRp = &rows[(src+1)*elemsPerRow];
    for (; srcRp != endRp; srcRp++) {

        

        if (*srcRp) {
            Elem tmp = *srcRp;
            while(tmp) {
                int p = __builtin_ctz(tmp);
                Elem m = 1 << p;
                *(cp + ((elemsPerRow - (int)(endRp - srcRp))*bitsPerElem + p) * elemsPerCol) ^= cm;
                tmp &= ~m;
            }
            *dstRp ^= *srcRp;
        }
        if (*dstRp) {
            Elem na = *nap & *dstRp;
            int bits = popcount(na);
            if (nonAss <= 1) {
                if (nonAss == 0 && bits) {
                    implied = (elemsPerRow - (int)(endRp - srcRp)) * bitsPerElem + 
                        __builtin_ctz(na);
                }

                parity ^= *vp & ~(*nap) & *dstRp;
            }
            nonAss += bits;


        }
        nap++;
        vp++;

        dstRp++;

//        cp += bitsPerElem * elemsPerCol;
    }

    naCount[dst] = nonAss;
#ifdef DEBUG
                {
    Elem* rp = &rows[dst*elemsPerRow];
    Elem* nap = nonAssigned;
    int nonAss = 0;
    for (int count = elemsPerRow; count > 0; count--) {
        if ( *rp) {
            Elem na = *nap & *rp;
            nonAss += popcount(na);
        }
        nap++;
        rp++;
    }

    cout << " nonAss " << nonAss << " naCnt[" << dst << "] " << naCount[dst] << endl;
    assert(nonAss == naCount[dst]);
                }

#endif

#ifdef DEBUG
                {

    for (int y = 0; y < height; y++) {
    Elem* rp = &rows[y*elemsPerRow];
    Elem* nap = nonAssigned;
    int nonAss = 0;
    for (int count = elemsPerRow; count > 0; count--) {
        if ( *rp) {
            Elem na = *nap & *rp;
            nonAss += popcount(na);
        }
        nap++;
        rp++;
    }

    cout << " nonAss " << nonAss << " naCnt[" << y << "] " << naCount[y] << endl;
    assert(nonAss == naCount[y]);
    }
                }

#endif

    switch(nonAss) {
        case 0:
            D("all assigned: parity : " <<
            (popcount(parity)&1));

            return (popcount(parity)&1) ? INT_MAX : 0;
            break;
        case 1:
            return (popcount(parity)&1) ? implied : -implied;
            break;
    }
    return 0;
}

void Matrix::swap(bool rowsOrCols, int r1, int r2) {

    int elsPerRow = rowsOrCols ? elemsPerRow : elemsPerCol;
    int elsPerCol = rowsOrCols ? elemsPerCol : elemsPerRow;
    Elem* rows_ = rowsOrCols ? rows : cols;
    Elem* cols_ = rowsOrCols ? cols : rows;

    Elem* r1p = &rows_[r1*elsPerRow];
    Elem* r2p = &rows_[r2*elsPerRow];
    Elem* c1p = cols_ + r1 / bitsPerElem;
    Elem* c2p = cols_ + r2 / bitsPerElem;
    int bp1 = r1 % bitsPerElem;
    int bp2 = r2 % bitsPerElem;
    if (bp1 > bp2) {
        Elem* tmp = c1p;
        c1p = c2p;
        c2p = tmp;
        int tmp2 = bp1;
        bp1 = bp2;
        bp2 = tmp2;
    }
    int bdist = bp2 - bp1;
    Elem b1m = 1<<bp1;
    Elem b2m = 1<<bp2;

    for (int count = elsPerRow; count > 0; count--) {
        Elem tmp = *r1p;
        *r1p = *r2p;
        *r2p = tmp;

        tmp |= *r1p;
        while (tmp) {
            int p = __builtin_ctz(tmp);
            Elem m = 1 << p;
            tmp &= ~m;
            Elem* c1lp = c1p + p * elsPerCol;
            Elem* c2lp = c2p + p * elsPerCol;
            Elem b1 = *c1lp & b1m;
            Elem b2 = *c2lp & b2m;
            Elem nb1 = b2 >> bdist;
            Elem nb2 = b1 << bdist;
            *c1lp ^= nb1 ^ b1;
            *c2lp ^= nb2 ^ b2;         
        }
        c1p += bitsPerElem * elsPerCol;
        c2p += bitsPerElem * elsPerCol;
        r1p++;
        r2p++;
    }
}
void Matrix::swapRows(int r1, int r2) {
    return;
    swap(true, r1, r2);
}

void Matrix::swapCols(int c1, int c2) {
    return;
    swap(false, c1, c2);
}
int Matrix::numOnesCol(int col) const {
    Elem* cp = &cols[col * elemsPerCol];
    int ones = 0;
    for (int count = elemsPerCol; count > 0; count--) {
        ones += popcount(*cp);
        cp++;
        
    }
    return ones;
}
int Matrix::numOnesRow(int row) const {
    assert(row >= 0 && row < height);

    Elem* rp = &rows[row * elemsPerRow];
    int ones = 0;
    for (int count = elemsPerRow; count > 0; count--) {
        ones += popcount(*rp);

        rp++;
        
    }
    return ones;
}


int Matrix::getValue(int x) const {
    assert(x >= 0 && x < width);

    Elem* nap = &nonAssigned[x / bitsPerElem];
    Elem m = 1 << (x % bitsPerElem);
    if (*nap & m) {
        return 0;
    } else {
        Elem* vp = &values[x / bitsPerElem];
        if (*vp & m)
            return 1;
        else
            return -1;
    } 
}
int Matrix::assign(int x, int value, 
                    vector<int>& implied_lits,
                    vector<int>& implied_by) {

    D("assign(" << x <<","<<value <<")");

#ifdef DEBUG
    {

        for (int y = 0; y < height; y++) {
            Elem* rp = &rows[y*elemsPerRow];
            Elem* nap = nonAssigned;
            int nonAss = 0;
            for (int count = elemsPerRow; count > 0; count--) {
                if ( *rp) {
                    Elem na = *nap & *rp;
                    nonAss += popcount(na);
                }
                nap++;
                rp++;
            }

            cout << " nonAss " << nonAss << " naCnt[" << y << "] " << naCount[y] << endl;
            assert(nonAss == naCount[y]);
        }
    }

#endif


    assert(x >= 0 && x < width);

    Elem* nap = &nonAssigned[x / bitsPerElem];
    Elem* vp = &values[x / bitsPerElem];
    Elem m = 1 << (x % bitsPerElem);
    if (!(*nap & m)) {
        if (((*vp & m)  > 0) != value)
            return UINT_MAX;
        return -1;
    }
    int conflict = -1;
    D("..ok");
    *nap &= ~m;
    if (value)
        *vp |= m;
    else
        *vp &= ~m;

    Elem* cp = &cols[x * elemsPerCol];
    Elem* endCp = &cols[(x+1) * elemsPerCol];
    for (; cp != endCp; cp++) {

        Elem tmp = *cp;

        while (tmp) {
            int p = __builtin_ctz(tmp);
            Elem m = 1 << p;
            tmp &= ~m;
            int y = (elemsPerCol - (int)(endCp - cp)) * bitsPerElem + p;
            naCount[y]--;
#ifdef DEBUG
            {
                Elem* rp = &rows[y*elemsPerRow];
                Elem* endRp = &rows[(y+1)*elemsPerRow];
                Elem* nap = nonAssigned;
                int nonAss = 0;
                for (; rp != endRp; rp++) {
                    if ( *rp) {
                        Elem na = *nap & *rp;
                        nonAss += popcount(na);
                    }
                    nap++;
                }

                cout << " nonAss " << nonAss << " naCnt[" << y << "] " << naCount[y] << endl;
                assert(nonAss == naCount[y]);
            }

#endif

            if (naCount[y] <= 1) {
                Elem* lrp = &rows[y* elemsPerRow];
                Elem* nap = nonAssigned;
                Elem* vp = values;


                if (naCount[y] == 0) {
                    // eager approach cannot end up in a conflict here!

                    /*
                    // non-zero row
                    Elem parity = 0;
                    Elem* endLrp = lrp + elemsPerRow;
                    for (; lrp != endLrp; lrp++) {
                        if (*lrp) {
                            // non-zero elem in the row
                            parity ^= *vp & ~(*nap) & *lrp;
                        } 
                        nap++;
                        vp++;
                    }
                    if (popcount(parity) & 1) {
                        D("conflict!");
                        conflict = (elemsPerCol - (int)(endCp - cp))*bitsPerElem + p;
                    }
                    */
                } else {
                    // non-zero row
                    int implied = 0;
                    Elem parity = 0;
                    Elem* endLrp = lrp + elemsPerRow;
                    for (; lrp != endLrp; lrp++) {
                        if (*lrp) {
                            // non-zero elem in the row
                            Elem na = *nap & *lrp;
                            if (na) {
                                implied = (elemsPerRow - 
                                        (int)(endLrp - lrp)) * bitsPerElem + 
                                    __builtin_ctz(na);
                            }
                            parity ^= *vp & ~(*nap) & *lrp;
                        } 
                        nap++;
                        vp++;
                    }
                    int value = popcount(parity) & 1;
                    // implied
                    int row = (elemsPerCol - (int)(endCp - cp))*bitsPerElem+p;
                    D("implied " << implied << " := " << value << " by "
                            << row);
                    implied_lits.push_back(value ? implied : -implied);
                    implied_by.push_back(row);
                    assert(implied_lits.size() == implied_by.size());
                    assert(implied_by.back() == row);

                }
            }
        }

    }

#ifdef DEBUG
    {

        for (int y = 0; y < height; y++) {
            Elem* rp = &rows[y*elemsPerRow];
            Elem* nap = nonAssigned;
            int nonAss = 0;
            for (int count = elemsPerRow; count > 0; count--) {
                if ( *rp) {
                    Elem na = *nap & *rp;
                    nonAss += popcount(na);
                }
                nap++;
                rp++;
            }

            cout << " nonAss " << nonAss << " naCnt[" << y << "] " << naCount[y] << endl;
            assert(nonAss == naCount[y]);
        }
    }

#endif


    return conflict;
}
int Matrix::pivot(int x, int y, std::vector<int>& implied_lits,
        vector<int>& implied_by) {
    Elem* cp = &cols[x * elemsPerCol];
    Elem* rp = rows;
    int baseRow = 0;
    for (int count = elemsPerCol; count > 0; count--) {

        if (*cp) {
            Elem tmp = *cp;

            while (tmp) {
                int p = __builtin_ctz(tmp);
                Elem m = 1 << p;
                tmp &= ~m;
                int row = baseRow + p;
                if (row != y) {

                    int implied = addRow(y, row);
                    if (implied) {
                        if (implied == INT_MAX)
                            return row;
                        D("pivot implied " << implied << " by " << row);
                        implied_lits.push_back(implied);
                        implied_by.push_back(row);

                    }
                }

            }
        }
        baseRow += bitsPerElem;
        rp += bitsPerElem * elemsPerRow;
        cp++;
    }
    return -1;
}

int Matrix::set_backtrack_point() {
    Elem* na = naAlloc.alloc(); //(Elem*) malloc(elemsPerRow * sizeof(Elem));
    memcpy(na, nonAssigned, sizeof(Elem) * elemsPerRow);
    nonAssignedCopies.push_back(na);

    return nonAssignedCopies.size() - 1;
}
void Matrix::incNaCount(int x) {
    Elem* cp = &cols[x * elemsPerCol];
    Elem* endCp = &cols[(x+1) * elemsPerCol];
    for (; cp != endCp; cp++) {
        Elem tmp = *cp;
        while (tmp) {
            int p = __builtin_ctz(tmp);
            Elem m = 1 << p;
            tmp &= ~m;

            naCount[(elemsPerCol - (int)(endCp - cp))*bitsPerElem+p]++;
        }
        //            *tp |= *cp;
        //        tp++;
    }
}
void Matrix::backtrack(int bt) {
    assert(bt >= 0 && bt < (int)nonAssignedCopies.size());
//    memcpy(nonAssigned, nonAssignedCopies[bt], sizeof(Elem) * elemsPerRow);

    Elem *newNap = nonAssignedCopies[bt];
    Elem *oldNap = nonAssigned;
    Elem* oldNonAssigned = nonAssigned;

    nonAssigned = nonAssignedCopies[bt];
    Elem* endNap = newNap + elemsPerRow;
    for (; newNap != endNap; newNap++) {
        Elem diff = *newNap ^ *oldNap;
        while(diff) {
            int p = __builtin_ctz(diff);
            Elem m = 1 << p;
            diff &= ~m;
            incNaCount((elemsPerRow-(int)(endNap - newNap))*bitsPerElem + p);

        }
        oldNap++;
    }

        
//    free(oldNonAssigned);
    naAlloc.dealloc(oldNonAssigned);
    for (int i = bt+1; i <(int) nonAssignedCopies.size(); i++) {
        naAlloc.dealloc(nonAssignedCopies[i]);
//        free(nonAssignedCopies[i]);
    }
    nonAssignedCopies.resize(bt);

#ifdef DEBUG
                {

    for (int y = 0; y < height; y++) {
    Elem* rp = &rows[y*elemsPerRow];
    Elem* nap = nonAssigned;
    int nonAss = 0;
    for (int count = elemsPerRow; count > 0; count--) {
        if ( *rp) {
            Elem na = *nap & *rp;
            nonAss += popcount(na);
        }
        nap++;
        rp++;
    }

    cout << " nonAss " << nonAss << " naCnt[" << y << "] " << naCount[y] << endl;
    assert(nonAss == naCount[y]);
    }
    cout << "backtrack ok" << endl;
                }

#endif

    
}


