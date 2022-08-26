//
// Created by xuanshu on 2022/06/17.
//
#include "FluidField.h"
#include <GL/glut.h>
#include <math.h>


#define IX(i, j) ((i) + (_n + 2) * (j))
#define SWAP(x0, x)      \
    {                    \
        float *tmp = x0; \
        x0 = x;          \
        x = tmp;         \
    }


bool FluidField::allocate() {
    int size = (_n + 2) * (_n + 2);
    _u = (float *)malloc(size * sizeof(float));
    _v = (float *)malloc(size * sizeof(float));
    _uPrev = (float *)malloc(size * sizeof(float));
    _vPrev = (float *)malloc(size * sizeof(float));
    _density = (float *)malloc(size * sizeof(float));
    _densityPrev = (float *)malloc(size * sizeof(float));
    if (!_u || !_v || !_uPrev || !_vPrev || !_density || !_densityPrev) {
        fprintf(stderr, "cannot allocate data\n");
        return false;
    }
    return true;
}

FluidField::FluidField(UseCase* uc, int nGrid) :
    _uc(uc), _dt(0.1f), _diff(0.0f), _visc(0.0f), _n(nGrid) {
    assert(allocate());
    int i, j, size = (nGrid + 2) * (nGrid + 2);
    for (i = 0; i < size; i++) {
        _u[i] = _v[i] = _density[i] = 0.0f;
    }
}

void FluidField::simulationStep() {
    velStep();
    densStep();
    vorticityConfinement();
}

void FluidField::addSource(float *x, const float *s) const {
    int i, size = (_n + 2) * (_n + 2);
    for (i = 0; i < size; i++) {
        x[i] += _dt * s[i];
    }
}

void FluidField::setBnd(int b, float *x) {
    // Gauss-Seidel relaxiation
    for (int i = 1; i <= _n; i++) {
        x[IX(0, i)] = b == 1 ? -x[IX(1, i)] : x[IX(1, i)];        // set upper boundary
        x[IX(_n + 1, i)] = b == 1 ? -x[IX(_n, i)] : x[IX(_n, i)]; // set lower boundary
        x[IX(i, 0)] = b == 2 ? -x[IX(i, 1)] : x[IX(i, 1)];        // set lhs boundary
        x[IX(i, _n + 1)] = b == 2 ? -x[IX(i, _n)] : x[IX(i, _n)]; // set rhs boundary
    }
    x[IX(0, 0)] = 0.5f * (x[IX(1, 0)] + x[IX(0, 1)]);                       //set _density of top left
    x[IX(0, _n + 1)] = 0.5f * (x[IX(1, _n + 1)] + x[IX(0, _n)]);            //set _density of top right
    x[IX(_n + 1, 0)] = 0.5f * (x[IX(_n, 0)] + x[IX(_n + 1, 1)]);            //set _density of bottom left
    x[IX(_n + 1, _n + 1)] = 0.5f * (x[IX(_n, _n + 1)] + x[IX(_n + 1, _n)]); //set _density of bottom right
}

void FluidField::linSolve(int b, float *x, const float *x0, float a, float c) {
    for (int k = 0; k < 20; k++) {
        for (int i = 1; i <= _n; i++) {
            for (int j = 1; j <= _n; j++) {
                x[IX(i, j)] = (x0[IX(i, j)] + a * (x[IX(i - 1, j)] + x[IX(i + 1, j)] + x[IX(i, j - 1)] + x[IX(i, j + 1)])) / c;
            }
        }
        setBnd(b, x);
    }
}

void FluidField::diffuse(int b, float *x, float *x0, float diff) {
    float a = _dt * diff * _n * _n; //apply stable diffusion "a"
    linSolve(b, x, x0, a, 1 + 4 * a);
}

void FluidField::advect(int b, float *d, float *d0, float *u, float *v) {
    int i0, j0, i1, j1;
    float x, y, s0, t0, s1, t1, dt0;
    dt0 = _dt * _n;
    for (int i = 1; i <= _n; i++) {
        for (int j = 1; j <= _n; j++) {
            x = i - dt0 * u[IX(i, j)];
            if (x < 0.5f)
                x = 0.5f; //top boundary limit
            if (x > _n + 0.5f)
                x = _n + 0.5f; //bottom boundary limit
            i0 = (int)x;      //get cell id of traced back x
            i1 = i0 + 1;      //get cell id of next step
            y = j - dt0 * v[IX(i, j)];
            if (y < 0.5f)
                y = 0.5f; //left boundary limit
            if (y > _n + 0.5f)
                y = _n + 0.5f; //right boundary limit
            j0 = (int)y;      //get cell id of traced back y
            j1 = j0 + 1;      //get cell id of next step
            s1 = x - i0;
            s0 = 1 - s1; //i0+1-x
            t1 = y - j0;
            t0 = 1 - t1; //j0+1-y
            d[IX(i, j)] = s0 * (t0 * d0[IX(i0, j0)] +
                                t1 * d0[IX(i0, j1)]) +
                          s1 * (t0 * d0[IX(i1, j0)] +
                                t1 * d0[IX(i1, j1)]);
        }
    }
    setBnd(b, d);
}

void FluidField::project(float *u, float *v, float *p, float *div) {
    for (int i = 1; i <= _n; i++) {
        for (int j = 1; j <= _n; j++) {
            div[IX(i, j)] = -0.5f * (u[IX(i + 1, j)] - u[IX(i - 1, j)] + v[IX(i, j + 1)] - v[IX(i, j - 1)]) / _n; //velocity function
            p[IX(i, j)] = 0;                                                                                     //pressure states/field
        }
    }
    setBnd(0, div);
    setBnd(0, p);
    linSolve(0, p, div, 1, 4);
    for (int i = 1; i <= _n; i++) {
        for (int j = 1; j <= _n; j++) {
            u[IX(i, j)] -= 0.5f * _n * (p[IX(i + 1, j)] - p[IX(i - 1, j)]);
            v[IX(i, j)] -= 0.5f * _n * (p[IX(i, j + 1)] - p[IX(i, j - 1)]);
        }
    }
    setBnd(1, u);
    setBnd(2, v);
}

void FluidField::vorticityConfinement() {
    float *curl = _densityPrev;
    float x, y, z;
    for (int i = 1; i <= _n; i++) {
        for (int j = 1; j <= _n; j++) {
            //totalDens += this.dens[IX(i,j)];
            // curlx = dw/dy - dv/dz
            x = (_u[IX(i + 1, j)] - _u[IX(i - 1, j)]) * 0.5;
            // curly = du/dz - dw/dx
            y = (_v[IX(i, j + 1)] - _v[IX(i, j - 1)]) * 0.5;
            // curlz = dv/dx - du/dy
            z = 0;
            // curl = |curl|
            curl[IX(i, j)] = sqrt(x * x + y * y + z * z);
        }
    }
    //add _vorticity confinement
    float Nx, Ny, len;
    for (int i = 1; i <= _n; i++) {
        for (int j = 1; j < _n; j++) {
            Nx = (curl[IX(i + 1, j)] - curl[IX(i - 1, j)]) * 0.5;
            Ny = (curl[IX(i, j + 1)] - curl[IX(i, j - 1)]) * 0.5;
            //normalize
            len = 1 / (sqrt(Nx * Nx + Ny * Ny) + 0.0000000000000000001);
            Nx *= len;
            Ny *= len;
            _u[IX(i, j)] += Nx * _uPrev[IX(i, j)];
            _v[IX(i, j)] += Ny * _vPrev[IX(i, j)];
        }
    }
}

void FluidField::densStep() {
    addSource(_density, _densityPrev);
    SWAP(_densityPrev, _density);
    diffuse(0, _density, _densityPrev, _diff);
    SWAP(_densityPrev, _density);
    advect(0, _density, _densityPrev, _u, _v);
}

void FluidField::velStep() {
    addSource(_u, _uPrev);
    addSource(_v, _vPrev);
    SWAP(_uPrev, _u);
    diffuse(1, _u, _uPrev, _visc);
    SWAP(_vPrev, _v);
    diffuse(2, _v, _vPrev, _visc);
    project(_u, _v, _uPrev, _vPrev);
    SWAP(_uPrev, _u);
    SWAP(_vPrev, _v);
    advect(1, _u, _uPrev, _uPrev, _vPrev);
    advect(2, _v, _vPrev, _uPrev, _vPrev);
    project(_u, _v, _uPrev, _vPrev);
}

void FluidField::drawVelocity() {
    int i, j;
    float x, y, h;
    h = 2.0f / _n;
    glColor3f(1.0f, 1.0f, 1.0f);
    glLineWidth(1.0f);
    glBegin(GL_LINES);
    for (i = 1; i <= _n; i++) {
        x = (i - 0.5f) * h;
        x = -1 + x;
        for (j = 1; j <= _n; j++) {
            y = (j - 0.5f) * h;
            y = -1 + y;
            glVertex2f(x, y);
            glVertex2f(x + _u[IX(i, j)], y + _v[IX(i, j)]);
        }
    }
    glEnd();
}

void FluidField::drawDensity() {
    int i, j;
    float x, y, h, d00, d01, d10, d11;
    h = 2.0f / _n;
    glBegin(GL_QUADS);
    for (i = 0; i <= _n; i++) {
        x = (i - 0.5f) * h;
        x = -1 + x;
        for (j = 0; j <= _n; j++) {
            y = (j - 0.5f) * h;
            y = -1 + y;
            d00 = _density[IX(i, j)];
            d01 = _density[IX(i, j + 1)];
            d10 = _density[IX(i + 1, j)];
            d11 = _density[IX(i + 1, j + 1)];
            glColor3f(d00, d00, d00);
            glVertex2f(x, y);
            glColor3f(d10, d10, d10);
            glVertex2f(x + h, y);
            glColor3f(d11, d11, d11);
            glVertex2f(x + h, y + h);
            glColor3f(d01, d01, d01);
            glVertex2f(x, y + h);
        }
    }
    glEnd();
}

void FluidField::freeData() {
    // for gird based system
    if (_u)
        free(_u);
    if (_v)
        free(_v);
    if (_uPrev)
        free(_uPrev);
    if (_vPrev)
        free(_vPrev);
    if (_density)
        free(_density);
    if (_densityPrev)
        free(_densityPrev);
}

void FluidField::reset() {
    // for gird based system
    int i, size = (_n + 2) * (_n + 2);
    for (i = 0; i < size; i++) {
        _u[i] = _v[i] = _uPrev[i] = _vPrev[i] = _density[i] = _densityPrev[i] = 0.0f;
    }
}
