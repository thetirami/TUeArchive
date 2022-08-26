//
// Created by xuanshu on 2022/06/17.
//

#pragma once
#include "Particle.h"
#include "UseCase.h"

class UseCase;
class FluidField {
private:
    UseCase* _uc;
    float _dt;
    float* _density;
    float* _densityPrev;
    float* _u;
    float* _uPrev;
    float* _v;
    float* _vPrev;
    float _vorticity;
    float _diff;
    float _visc;
    float _width;
    float _height;
    int _n;

public:
    FluidField(UseCase *uc, int nGrid);
    void simulationStep();
    void addSource(float *x, const float *s) const;
    void setBnd(int b, float *x);
    void linSolve(int b, float *x, const float *x0, float a, float c);
    void diffuse(int b, float *x, float *x0, float diff);
    void advect(int b, float *d, float *d0, float *u, float *v);
    void project(float *u, float *v, float *p, float *div);
    void vorticityConfinement();
    void densStep();
    void velStep();
    void drawDensity();
    void drawVelocity();
    bool allocate();
    void freeData();
    void reset();
};