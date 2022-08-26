#pragma once

#include <vector>
#include "Particle.h"
#include "constraint/Constraint.h"


class FixedConstraint : public Constraint {
private:
    Particle *const _p;
    Vec2f const _center;
public:
    FixedConstraint(Particle *p, const Vec2f& center);
    std::vector<Particle*> p() override {
        return {_p};
    }
    float C() override {
        Vec2f pVec = _p->pos() - _center;
        return pVec * pVec / 2;
    }
    float legalV() override {
        Vec2f pVec = _p->pos() - _center;
        Vec2f vVec = _p->v();
        return pVec * vVec;
    }
    std::vector<Vec2f> jacobian() override {
        std::vector<Vec2f> j;
        j.push_back(_p->pos() - _center);
        return j;
    }
    std::vector<Vec2f> dJacobian() override {
        std::vector<Vec2f> dj;
        dj.push_back(_p->v());
        return dj;
    }
    void draw() override;
};

