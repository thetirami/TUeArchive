//
// Created by xuanshu on 2022/06/17.
//

#pragma once
#include "Particle.h"

class Fluid {
private:
    float _h;
    float* _density;
    float* _densityPrev;
    float* _u;
    float* _uPrev;
    float* _v;
    float* _vPrev;
    float _vorticity;
    float _width;
    float _height;
    int _n;
    int _size = (_n + 2) * (_n + 2);
    std::vector<Particle*> _rigidBody;
public:
    Fluid() = default;
    std::vector<Particle*> p() {
        return _rigidBody;
    }
    void setRParticle(std::vector<Particle*> p) {
        _rigidBody = p;
    }
    void addSource(int N, float *x, const float *s, float dt);
    void setBnd(int N, int b, float *x);
    int checkInner(int i, int j, std::vector<Eigen::Vector2i> pos);
    void linSolve(int N, int b, float *x, const float *x0, float a, float c);
    void diffuse(int N, int b, float *x, float *x0, float diff, float dt);
    void advect(int N, int b, float *d, float *d0, float *u, float *v, float dt);
    void project(int N, float *u, float *v, float *p, float *div);
    void vorticityConfinement(int N, float dt, float *d0, float *u, float *v, float *u0, float *v0);
    void setDensity(float *d, float *dprev, int inputN);
    float getDensity(int i, int j);
    void setVelocity(float *xu, float *xv, float *xuprev, float *xvprev, int inputN);
    float getXVelocity(int i, int j);
    float getYVelocity(int i, int j);
    void densStep(int N, float *x, float *x0, float *u, float *v, float diff, float dt);
    void velStep(int N, float *u, float *v, float *u0, float *v0, float visc, float dt);
};