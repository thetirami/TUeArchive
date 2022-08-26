//
// Created by xuanshu on 2022/05/27.
//

#include "force/AngularSpringForce.h"

AngularSpringForce::AngularSpringForce(Particle *p1, Particle *p2, Particle *p3, float angle, float ks, float kd) :
    _p1(p1), _p2(p2), _p3(p3), _angle(angle), _ks(ks), _kd(kd) {

}

