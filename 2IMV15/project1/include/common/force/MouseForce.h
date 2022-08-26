#pragma once

#include "force/Force.h"

class MouseForce : public Force {
private:
    Particle* _p;
    Vec2f _direction;
    float _f;
    bool _active = true;
public:
    MouseForce(Particle *p, Vec2f direction, float f);
    void active(bool state) {
        _active = state;
    }
    bool isActive() const {
        return _active;
    }
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
    void setDirection(Vec2f direction) {
        _direction = direction;
    }
    void apply() override {
        if (_active) {
            _p->updateF(_direction * _f);
        }
    }
    void draw() override {

    }
};
