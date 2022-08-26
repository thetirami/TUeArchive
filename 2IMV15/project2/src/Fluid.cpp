//
// Created by xuanshu on 2022/06/17.
//
#include "Fluid.h"
#include <cmath>


#define IX(i, j) ((i) + (N + 2) * (j))
#define SWAP(x0, x)      \
    {                    \
        float *tmp = x0; \
        x0 = x;          \
        x = tmp;         \
    }

void Fluid::addSource(int N, float *x, const float *s, float dt) {
    _h = dt;
    int i, size = (N + 2) * (N + 2);
    for (i = 0; i < size; i++) {
        x[i] += dt * s[i];
    }
}

void Fluid::setBnd(int N, int b, float *x) {
    // Gauss-Seidel relaxation
    for (int i = 1; i <= N; i++) {
        x[IX(0, i)] = b == 1 ? -x[IX(1, i)] : x[IX(1, i)];     //if b==1, upper boundary
        x[IX(N + 1, i)] = b == 1 ? -x[IX(N, i)] : x[IX(N, i)]; //if b==1, lower boundary
        x[IX(i, 0)] = b == 2 ? -x[IX(i, 1)] : x[IX(i, 1)];     //if b==2, lhs boundary
        x[IX(i, N + 1)] = b == 2 ? -x[IX(i, N)] : x[IX(i, N)]; //if b==2, rhs boundary
    }
    x[IX(0, 0)] = 0.5f * (x[IX(1, 0)] + x[IX(0, 1)]);                 //set _density of top left corner cell
    x[IX(0, N + 1)] = 0.5f * (x[IX(1, N + 1)] + x[IX(0, N)]);         //set _density of top right corner cell
    x[IX(N + 1, 0)] = 0.5f * (x[IX(N, 0)] + x[IX(N + 1, 1)]);         //set _density of bottom left corner cell
    x[IX(N + 1, N + 1)] = 0.5f * (x[IX(N, N + 1)] + x[IX(N + 1, N)]); //set _density of bottom right corner cell
    //internal boundary to deal with _rigidBody->fluid
    for (Particle *rigidBody : _rigidBody) {
        // cout<<"rigid_corners"<< rigidBody->corners[0]<<" "<< rigidBody->corners[1]<<" "<< rigidBody->corners[2]<<" "<< rigidBody->corners[3]<<" "<<endl;
        std::vector<Eigen::Vector4f> boundgrids = rigidBody->boundGrid(N);
        std::vector<Eigen::Vector2i> innergrids = rigidBody->innerGrid(boundgrids);
        for (auto & boundgrid : boundgrids) {
            //if case1: first flip fluid value(Gauss-Seidel relaxiation),
            //then if rigid grid is on upper/lower canvas boundary, fluid value is changed based on x velocity field
            //if rigid grid is on lhs/rhs canvas boundary, fluid value is changed based on y velocity field
            if (b == 1 || b == 2) {
                x[IX((int)boundgrid[0], (int)boundgrid[1])] *= -1; //flip velocity
                Eigen::Vector2f vel = rigidBody->v();
                float factor = _h * 0.05;
                //if the grid is also on canvas boundary
                if (b == 1) {
                    x[IX((int)boundgrid[0], (int)boundgrid[1])] += vel[0] * factor;
                } else if (b == 2) {
                    x[IX((int)boundgrid[0], (int)boundgrid[1])] += vel[1] * factor;
                }
            } else {
                // assign average value of fluid neighboring cells(grids) to current cell
                float before = (checkInner((int) boundgrid[0] - 1, (int) boundgrid[1], innergrids) == 1) ? 0 : 1;
                float after = (checkInner((int) boundgrid[0] + 1, (int) boundgrid[1], innergrids) == 1) ? 0 : 1;
                float above = (checkInner((int) boundgrid[0], (int) boundgrid[1] + 1, innergrids) == 1) ? 0 : 1;
                float below = (checkInner((int) boundgrid[0], (int) boundgrid[1] - 1, innergrids) == 1) ? 0 : 1;
                float x_before = (before == 1) ? x[IX((int)boundgrid[0] - 1, (int)boundgrid[1])] : 0;
                float x_after = (after == 1) ? x[IX((int)boundgrid[0] + 1, (int)boundgrid[1])] : 0;
                float x_above = (above == 1) ? x[IX((int)boundgrid[0], (int)boundgrid[1] + 1)] : 0;
                float x_below = (below == 1) ? x[IX((int)boundgrid[0], (int)boundgrid[1] - 1)] : 0;
                x[IX((int)boundgrid[0], (int)boundgrid[1])] = (x_before + x_after + x_above + x_below) / (before + after + above + below);
            }
        }
        // for all fluid grids inside rigid body, assign 0
        for (auto & innergrid : innergrids) {
            x[IX((int)innergrid[0], (int)innergrid[1])] = 0;
        }
    }
}

int Fluid::checkInner(int i, int j, std::vector<Eigen::Vector2i> pos) {
    for (auto & po : pos) {
        if (i == po[0] && j == po[1]) {
            return 1;
        }
    }
    return 0;
}

void Fluid::linSolve(int N, int b, float *x, const float *x0, float a, float c) {
    for (int k = 0; k < 20; k++) {
        for (int i = 1; i <= N; i++) {
            for (int j = 1; j <= N; j++) {
                //for each not boundary cell, give it back-diffusion(stable) _density/...
                x[IX(i, j)] = (x0[IX(i, j)] + a * (x[IX(i - 1, j)] + x[IX(i + 1, j)] + x[IX(i, j - 1)] + x[IX(i, j + 1)])) / c;
            }
        }
        setBnd(N, b, x); //set densities
    }
}

void Fluid::diffuse(int N, int b, float *x, float *x0, float diff, float dt) {
    float a = dt * diff * N * N; //apply stable diffusion "a"
    linSolve(N, b, x, x0, a, 1 + 4 * a);
}

void Fluid::advect(int N, int b, float *d, float *d0, float *u, float *v, float dt) {
    int i0, j0, i1, j1;
    float x, y, s0, t0, s1, t1, dt0;

    dt0 = dt * N;
    for (int i = 1; i <= N; i++) {
        for (int j = 1; j <= N; j++) {
            x = i - dt0 * u[IX(i, j)];
            if (x < 0.5f)
                x = 0.5f; //top boundary limit
            if (x > N + 0.5f)
                x = N + 0.5f; //bottom boundary limit
            i0 = (int)x;      //get cell id of traced back x
            i1 = i0 + 1;      //get cell id of next step
            y = j - dt0 * v[IX(i, j)];
            if (y < 0.5f)
                y = 0.5f; //left boundary limit
            if (y > N + 0.5f)
                y = N + 0.5f; //right boundary limit
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
    setBnd(N, b, d);
}

void Fluid::project(int N, float *u, float *v, float *p, float *div) {
    //velocity field = mass conservation + velocity gradient
    for (int i = 1; i <= N; i++) {
        for (int j = 1; j <= N; j++) {
            div[IX(i, j)] = -0.5f * (u[IX(i + 1, j)] - u[IX(i - 1, j)] + v[IX(i, j + 1)] - v[IX(i, j - 1)]) / N; //velocity function
            p[IX(i, j)] = 0;                                                                                     //pressure states/field
        }
    }
    setBnd(N, 0, div);
    setBnd(N, 0, p);
    // P state neighbors and velocity relations
    linSolve(N, 0, p, div, 1, 4);
    //velocity gradient = second derivative of P field
    for (int i = 1; i <= N; i++) {
        for (int j = 1; j <= N; j++) {
            u[IX(i, j)] -= 0.5f * N * (p[IX(i + 1, j)] - p[IX(i - 1, j)]);
            v[IX(i, j)] -= 0.5f * N * (p[IX(i, j + 1)] - p[IX(i, j - 1)]);
        }
    }
    setBnd(N, 1, u); //set velocity field
    setBnd(N, 2, v); //set velocity field
}

void Fluid::vorticityConfinement(int N, float dt, float *d0, float *u, float *v, float *u0, float *v0) {
    float *curl = d0;
    //compute _vorticity
    setDensity(_density, d0, N);
    setVelocity(u, v, u0, v0, N);
    float x, y, z;
    for (int i = 1; i <= N; i++) {
        for (int j = 1; j <= N; j++) {
            x = (u[IX(i + 1, j)] - u[IX(i - 1, j)]) * 0.5;
            y = (v[IX(i, j + 1)] - v[IX(i, j - 1)]) * 0.5;
            z = 0;
            curl[IX(i, j)] = sqrt(x * x + y * y + z * z);
        }
    }
    // confinement
    float Nx, Ny, len;
    for (int i = 1; i <= N; i++) {
        for (int j = 1; j < N; j++) {
            Nx = (curl[IX(i + 1, j)] - curl[IX(i - 1, j)]) * 0.5;
            Ny = (curl[IX(i, j + 1)] - curl[IX(i, j - 1)]) * 0.5;
            //normalize
            len = 1 / (sqrt(Nx * Nx + Ny * Ny) + 0.0000000000000000001);
            Nx *= len;
            Ny *= len;
            u[IX(i, j)] += dt * Nx * u0[IX(i, j)];
            v[IX(i, j)] += dt * Ny * v0[IX(i, j)];
        }
    }
}

void Fluid::setDensity(float *d, float *dprev, int inputN) {
    _density = d;
    _densityPrev = dprev;
    _n = inputN;
};

float Fluid::getDensity(int i, int j) {
    int idx = i + (_n + 2) * j;
    return *(_density + idx);
};

void Fluid::setVelocity(float *xu, float *xv, float *xuprev, float *xvprev, int inputN) {
    _u = xu;
    _v = xv;
    _uPrev = xuprev;
    _vPrev = xvprev;
    _n = inputN;
};

float Fluid::getXVelocity(int i, int j) {
    int idx = i + (_n + 2) * j;
    return *(_u + idx);
};

float Fluid::getYVelocity(int i, int j) {
    int idx = i + (_n + 2) * j;
    return *(_v + idx);
};

void Fluid::densStep(int N, float *x, float *x0, float *u, float *v, float diff, float dt) {
    // cout<<"hello "<<x0[IX(64, 82)]<<endl;
    setDensity(x, x0, N);
    addSource(N, x, x0, dt);
    SWAP(x0, x);
    diffuse(N, 0, x, x0, diff, dt);
    SWAP(x0, x);
    advect(N, 0, x, x0, u, v, dt);
    setDensity(x, x0, N);
}

void Fluid::velStep(int N, float *u, float *v, float *u0, float *v0, float visc, float dt) {
    setVelocity(u, v, u0, v0, N);
    addSource(N, u, u0, dt);
    addSource(N, v, v0, dt);
    SWAP(u0, u);
    diffuse(N, 1, u, u0, visc, dt);
    SWAP(v0, v);
    diffuse(N, 2, v, v0, visc, dt);
    project(N, u, v, u0, v0);
    SWAP(u0, u);
    SWAP(v0, v);
    advect(N, 1, u, u0, u0, v0, dt);
    advect(N, 2, v, v0, u0, v0, dt);
    project(N, u, v, u0, v0);
    setVelocity(u, v, u0, v0, N);
}
