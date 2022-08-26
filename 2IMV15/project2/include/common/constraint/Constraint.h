//
// Created by xuanshu on 2022/05/26.
//
#pragma once

#include <gfx/vec2.h>
#include "Particle.h"

class Constraint {
private:
public:
    virtual void draw() = 0;
    virtual std::vector<Particle*> p() = 0;
    virtual float C() = 0;
    virtual float legalV() = 0;
    virtual std::vector<Eigen::Vector2f> jacobian() = 0;
    virtual std::vector<Eigen::Vector2f> dJacobian() = 0;
};
