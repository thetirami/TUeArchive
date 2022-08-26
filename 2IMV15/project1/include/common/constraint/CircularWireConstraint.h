#pragma once

#include <vector>
#include "Particle.h"
#include "constraint/Constraint.h"

class CircularWireConstraint : public Constraint {
private:
    Particle *const _p;
    Vec2f const _center;
    double const _radius;
public:
    CircularWireConstraint(Particle *p, const Vec2f &center, double radius);
    std::vector<Particle*> p() override {
        return {_p};
    }
    float C() override {
        Vec2f diff = _p->pos() - _center;
        return diff * diff - _radius * _radius;
    }
    float legalV() override {
        Vec2f diff = _p->pos() - _center;
        return 2 * diff * _p->v();
    }
    std::vector<Vec2f> jacobian() override {
        std::vector<Vec2f> j;
        j.push_back((_p->pos() - _center) * 2);
        return j;
    }
    std::vector<Vec2f> dJacobian() override {
        std::vector<Vec2f> dj;
        dj.push_back(_p->v() * 2);
        return dj;
    }
    void draw() override;
};
