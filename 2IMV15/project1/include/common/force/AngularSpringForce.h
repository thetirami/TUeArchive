//
// Created by xuanshu on 2022/05/27.
//

#ifndef UNIFIED_MAKEFILE_PROJECT1_ANGULARSPRINGFORCE_H
#define UNIFIED_MAKEFILE_PROJECT1_ANGULARSPRINGFORCE_H

#pragma once

#include "force/Force.h"

class AngularSpringForce : public Force {
private:
    Particle* _p1;
    Particle* _p2; // middle
    Particle* _p3;
    float _angle; // cosine of the rest angle
    float _ks, _kd;
public:
    AngularSpringForce(Particle* p1, Particle* p2, Particle* p3, float angle, float ks, float kd);
    std::vector<Particle*> p() override {
        return {_p1, _p2, _p3};
    }
    Particle* p1() { return _p1; }
    Particle* p2() { return _p2; }
    Particle* p3() { return _p3; }
    std::map<int, std::map<int, float>> dx() override {
        return {};
    }
    void apply() override {
        Vec2f midtoP1 = _p1->pos() - _p2->pos();
        Vec2f P3tomid = _p2->pos() - _p3->pos();
        float cos_angle = (midtoP1 * P3tomid)/(norm(midtoP1) * norm(P3tomid));
        if (cos_angle > 1.0) cos_angle = 1.0;
        if (cos_angle < -1.0) cos_angle = -1.0;
        Vec2f length = _p1->pos() - _p3->pos();
        Vec2f velocity = _p1->v() - _p3->v();
        // Compute spring force
        double b = norm(midtoP1);
        double c = norm(P3tomid);
        Vec2f result = -(_ks * (norm(length) - sqrt(b*b+c*c-2*b*c*cos(_angle))) + _kd * ((length*velocity)/norm(length))) * (length / norm(length));
        _p1->updateF(result);
        _p3->updateF(-result);
    }
    Eigen::MatrixXf dv() override {
        return {};
    }
    void draw() override {

    }
};

#endif //UNIFIED_MAKEFILE_PROJECT1_ANGULARSPRINGFORCE_H
