#ifndef _matrix_hpp_
#define _matrix_hpp_
#include <stdint.h>
#include <malloc.h>
#include <iostream>
#include <vector>
template <class T> 
    class Allocator {

    std::vector<T*> blocks;
    std::vector<T*> elems;
    const int size;
    void newBlock() {
        T* b = (T*) malloc(100 * size * sizeof(T));

        blocks.push_back(b);
        for (size_t i = 0; i < 100; i++) {
            elems.push_back(&b[i*size]);

        }
    }
public:
    Allocator(int s) : size(s) {}
    ~Allocator() {
        for (size_t i = 0; i < blocks.size(); i++)
            free(blocks[i]);
    }
    T* alloc() {
        if (elems.empty())
            newBlock();
        T* e = elems.back();
        elems.pop_back();
        return e;
    }
    void dealloc(T* elem) {
        elems.push_back(elem);
    }
};

class Matrix {
    typedef uint32_t Elem;
    Elem* rows;
    Elem* cols;
    Elem* nonAssigned;
    Elem* values;
    int* naCount;
    std::vector<Elem*> nonAssignedCopies;

    const int width;
    const int height;
    static const int bitsPerElem;
    const int elemsPerRow;
    const int elemsPerCol;

    Allocator<Elem> naAlloc;

    Matrix(const Matrix& m);
    Matrix& operator=(const Matrix& m);

    void swap(bool rows, int r1, int r2);
    void incNaCount(int x);

public:
    Matrix(int width, int height);
    ~Matrix();
    void set(int x, int y, int value);
    int get(int x, int y) const;
    void getRow(int y, std::vector<int>& row);
    void getCol(int x, std::vector<int>& col);

    void getAssigned(int y, std::vector<int>& row);
    int getHeight() const {
        return height;
    }
    int getWidth() const {
        return width;
    }
    int addRow(int src, int dst);
    void swapRows(int r1, int r2);
    void swapCols(int c1, int c2);
    int numOnesCol(int col) const;
    int numOnesRow(int row) const;
    int getValue(int x) const;
    int assign(int x, int value, 
               std::vector<int>& implied,
               std::vector<int>& impliedBy);
    // eliminate other occurrences of 'x' by adding
    // row 'y' 
    int pivot(int x, int y, 
              std::vector<int>& implied,
              std::vector<int>& impliedBy);
    int set_backtrack_point();
    void backtrack(int bt);
};
#endif
