#pragma once

#include <vector>
#include "Particle.h"
#include "constraint/Constraint.h"

class RodConstraint : public Constraint {
private:
    Particle* _p1;
    Particle* _p2;
    double _dist;
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
    float legalV() override {
        Eigen::Vector2f pVec = (_p1->pos() - _p2->pos()) * 2;
        Eigen::Vector2f vVec = (_p1->v() - _p2->v()) * 2;
        return pVec.dot(vVec);
    }
    std::vector<Eigen::Vector2f> jacobian() override {
        std::vector<Eigen::Vector2f> j;
        j.emplace_back((_p1->pos() - _p2->pos()) * 2);
        j.emplace_back(-(_p1->pos() - _p2->pos()) * 2);
        return j;
    }
    std::vector<Eigen::Vector2f> dJacobian() override {
        std::vector<Eigen::Vector2f> dj;
        dj.emplace_back( (_p1->v() - _p2->v()) * 2);
        dj.emplace_back(-(_p1->v() - _p2->v()) * 2);
        return dj;
    }
    void draw() override;
};
