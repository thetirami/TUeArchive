//
// Created by xuanshu on 2022/05/26.
//
#pragma once

#include <vector>
#include <map>
#include "Particle.h"
#include "eigen/Core"

class Force {
private:
    bool _isActive = true;
public:
    ~Force() = default;
    void toggle() {
        _isActive = !_isActive;
    }
    bool isActive() const { return _isActive; }
    void setActive(bool active) {
        _isActive = active;
    }
    virtual std::vector<Particle*> p() = 0;
    virtual std::map<int, std::map<int, float>> dx() = 0;
    virtual Eigen::MatrixXf dv() = 0;
    virtual void apply() = 0;
    virtual void draw() = 0;
};
