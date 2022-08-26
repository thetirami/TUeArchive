//
// Created by xuanshu on 2022/05/26.
//

#ifndef UNIFIED_MAKEFILE_PROJECT1_FORCE_H
#define UNIFIED_MAKEFILE_PROJECT1_FORCE_H

#include <vector>
#include <map>
#include "Particle.h"
#include "eigen/Eigen/Core"

class Force {
private:
public:
    virtual std::vector<Particle*> p() = 0;
    virtual std::map<int, std::map<int, float>> dx() = 0;
    virtual Eigen::MatrixXf dv() = 0;
    virtual void apply() = 0;
    virtual void draw() = 0;
};

#endif //UNIFIED_MAKEFILE_PROJECT1_FORCE_H
