#pragma once

#include <vector>
#include "Particle.h"
#include "constraint/Constraint.h"

class RodConstraint : public Constraint {
private:
    Particle *const _p1;
    Particle *const _p2;
    double const _dist;
public:
    RodConstraint(Particle *p1, Particle *p2, double dist);
    std::vector<Particle*> p() override {
        return {_p1, _p2};
    }
    float C() override {
        float dx = _p1->pos(0) - _p2->pos(0);
        float dy = _p1->pos(1) - _p2->pos(1);
        return pow(dx, 2) + pow(dy, 2) - pow(_dist, 2);
    }
    float CVariation() {
        float dx = _p1->pos(0) - _p2->pos(0);
        float dy = _p1->pos(1) - _p2->pos(1);
        return sqrt(pow(dx, 2) + pow(dy, 2)) - _dist;
    }
    float legalV() override {
        Vec2f pVec = (_p1->pos() - _p2->pos()) * 2;
        Vec2f vVec = (_p1->v() - _p2->v()) * 2;
        return pVec * vVec;
    }
    std::vector<Vec2f> jacobian() override {
        std::vector<Vec2f> j;
        j.push_back( (_p1->pos() - _p2->pos()) * 2);
        j.push_back(-(_p1->pos() - _p2->pos()) * 2);
        return j;
    }
    std::vector<Vec2f> dJacobian() override {
        std::vector<Vec2f> dj;
        dj.push_back( (_p1->v() - _p2->v()) * 2);
        dj.push_back(-(_p1->v() - _p2->v()) * 2);
        return dj;
    }
    void draw() override;
};
