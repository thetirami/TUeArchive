#pragma once

#include <vector>
#include "Particle.h"
#include "constraint/Constraint.h"


class FixedConstraint : public Constraint {
private:
    Particle* _p;
    Eigen::Vector2f _center;
public:
    FixedConstraint(Particle *p, Eigen::Vector2f center);
    std::vector<Particle*> p() override {
        return {_p};
    }
    float C() override {
        Eigen::Vector2f pVec = _p->pos() - _center;
        return pVec.dot(pVec) / 2;
    }
    float legalV() override {
        Eigen::Vector2f pVec = _p->pos() - _center;
        Eigen::Vector2f vVec = _p->v();
        return pVec.dot(vVec);
    }
    std::vector<Eigen::Vector2f> jacobian() override {
        std::vector<Eigen::Vector2f> j;
        j.emplace_back(_p->pos() - _center);
        return j;
    }
    std::vector<Eigen::Vector2f> dJacobian() override {
        std::vector<Eigen::Vector2f> dj;
        dj.push_back(_p->v());
        return dj;
    }
    void draw() override;
};

