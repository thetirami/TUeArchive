#pragma once

#include <vector>
#include "Particle.h"
#include "constraint/Constraint.h"

class CircularWireConstraint : public Constraint {
private:
    Particle* _p;
    Eigen::Vector2f _center;
    double _radius;
public:
    CircularWireConstraint(Particle *p, Eigen::Vector2f center, double radius);
    std::vector<Particle*> p() override {
        return {_p};
    }
    float C() override {
        Eigen::Vector2f diff = _p->pos() - _center;
        return diff.dot(diff) - _radius * _radius;
    }
    float legalV() override {
        Eigen::Vector2f pVec = _p->pos() - _center;
        Eigen::Vector2f vVec = _p->v();
        return 2 * pVec.dot(vVec);
    }
    std::vector<Eigen::Vector2f> jacobian() override {
        std::vector<Eigen::Vector2f> j;
        j.emplace_back((_p->pos() - _center) * 2);
        return j;
    }
    std::vector<Eigen::Vector2f> dJacobian() override {
        std::vector<Eigen::Vector2f> dj;
        dj.emplace_back(_p->v() * 2);
        return dj;
    }
    void draw() override;
};
