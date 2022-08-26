#pragma once

#include "force/Force.h"

#include <utility>

class MouseForce : public Force {
private:
    Particle* _p;
    Eigen::Vector2f _direction;
    float _f;
public:
    MouseForce(Particle *p, Eigen::Vector2f direction, float f);
    std::vector<Particle*> p() override {
        return {_p};
    }
    Particle* pp() {
        return _p;
    }
    std::map<int, std::map<int, float>> dx() override {
        return {};
    }
    Eigen::MatrixXf dv() override {
        return {};
    }
    void setDirection(Eigen::Vector2f direction) {
        _direction = std::move(direction);
    }
    void apply() override {
        if (isActive()) {
            _p->updateF(_direction * _f);
        }
    }
    void draw() override {

    }
};
