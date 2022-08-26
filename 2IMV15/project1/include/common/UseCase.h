#pragma once

#include <vector>

#include "constraint/Constraint.h"
#include "force/Force.h"
#include "solver/Solver.h"
#include "eigen/Eigen/Dense"
#include "eigen/Eigen/IterativeLinearSolvers"

class Solver;
class UseCase {
private:
    Solver* _solver;
    std::vector<Constraint*> _c;
    std::vector<Force*> _f;
    std::vector<Particle*> _p;
    bool _wall = true;
    float _t = 0.0f;   // time
    float _dt = 0.001f;  // time step
public:
    explicit UseCase(Solver* solver);
    Constraint* c(int i) {
        return _c[i];
    }
    std::vector<Force*> f() {
        return _f;
    }
    Force* f(int i) {
        return _f[i];
    }
    std::vector<Particle*> p() {
        return _p;
    }
    Particle* p(int i) {
        return _p[i];
    }
    void addConstraint(Constraint* c) {
        _c.push_back(c);
    }
    void addForce(Force* f) {
        _f.push_back(f);
    }
    void addParticle(Particle* p) {
        _p.push_back(p);
    }
    int pDims() {
        return _p.size() * 2 * 2;
    }
    float t() const {
        return _t;
    }
    float dt() const {
        return _dt;
    }
    void setDt(float dt) {
        _dt = dt;
    }
    bool wall() const {
        return _wall;
    }
    void setWall(bool wall) {
        _wall = wall;
    }
    void setT(float time) {
        _t = time;
    }
    void setSolver(Solver* solver) {
        setS(solver);
    }
    void clean() {
        _f.clear();
        _p.clear();
    }
    void applyF() {
        for (auto f : _f) {
            f->apply();
        }
    }
    void cleanF() {
        for (auto p : _p) {
            p->setF(Vec2f(0.0, 0.0));
        }
    }
    void reset() {
        for (auto p : _p) {
            p->reset();
        }
    }

    Eigen::VectorXf getState();
    void setState(Eigen::VectorXf s, float t);
    Eigen::VectorXf dParticle();
    void maintainConstraint(float ks, float kd);
    template<class T>void setS(T t){};
    Eigen::VectorXf aParticle() {
        cleanF();
        applyF();
        maintainConstraint(0.0f, 0.0f);
        return dParticle();
    }
    Eigen::VectorXf wallCollision(Eigen::VectorXf state) {
        for (int i = 0; i < _p.size(); i++) {
            if (state[i * 4] < -0.9f) {
                state[i * 4] = -0.9f;
                state[i * 4 + 2] = -state[i * 4 + 2];
            }
            if (state[i * 4] > 0.9f) {
                state[i * 4] = 0.9f;
                state[i * 4 + 2] = -state[i * 4 + 2];
            }
            if (state[i * 4 + 1] < -0.9f) {
                state[i * 4 + 1] = -0.9f;
                state[i * 4 + 3] = -state[i * 4 + 3];
            }
            if (state[i * 4 + 1] > 0.9f) {
                state[i * 4 + 1] = 0.9f;
                state[i * 4 + 3] = -state[i * 4 + 3];
            }
        }
        return state;
    }
    void simulationStep();
    void drawC() {
        for (auto c : _c) {
            c->draw();
        }
    }
    void drawF() {
        for (auto f : _f) {
            f->draw();
        }
    }
    void drawP() {
        for (auto p : _p) {
            p->draw();
        }
    }
};

