#pragma once

#include <vector>

#include "constraint/Constraint.h"
#include "force/Force.h"
#include "solver/Solver.h"
#include "Fluid.h"
#include "eigen/Core"
#include "eigen/IterativeLinearSolvers"

class Solver;
class UseCase {
private:
    Solver* _solver;
    Fluid *_fluid;
    std::vector<Constraint*> _c;
    std::vector<Force*> _f;
    std::vector<Force*> _rf;    // rigid
    std::vector<Particle*> _p;
    std::vector<Particle*> _rp; // rigid
    bool _wall = true;
    float _t = 0.0f;   // time
    float _dt = 0.001f;  // time step
public:
    explicit UseCase(Solver* solver, Fluid* fluid);
    Constraint* c(int i) {
        return _c[i];
    }
    std::vector<Force*> f() {
        return _f;
    }
    Force* f(int i) {
        return _f[i];
    }
    std::vector<Force*> rf() {
        return _rf;
    }
    Force* rf(int i) {
        return _rf[i];
    }
    std::vector<Particle*> p() {
        return _p;
    }
    Particle* p(int i) {
        return _p[i];
    }
    std::vector<Particle*> rp() {
        return _rp;
    }
    Particle* rp(int i) {
        return _rp[i];
    }
    void addConstraint(Constraint* c) {
        _c.push_back(c);
    }
    void addForce(Force* f) {
        _f.push_back(f);
    }
    void addRigidForce(Force* f) {
        _rf.push_back(f);
    }
    void addParticle(Particle* p) {
        if (p->type() == NORMAL)
            _p.push_back(p);
    }
    void addRigidParticle(Particle* p) {
        if (p->type() != NORMAL)
            _rp.push_back(p);
    }
    int pDims() {
        return _p.size() * 2 * 2;
    }
    int rpDims() {
        return _rp.size() * 8;
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
    void clean() {
        _f.clear();
        _p.clear();
        _rp.clear();
    }
    void applyF() {
        for (auto f : _f) {
            f->apply();
        }
    }
    void applyRF() {
        for (auto f : _rf) {
            f->apply();
        }
    }
    void cleanF() {
        for (auto p : _p) {
            p->setF(Eigen::Vector2f(0.0, 0.0));
        }
    }
    void cleanRF() {
        for (auto p : _rp) {
            p->setF(Eigen::Vector2f(0.0, 0.0));
            p->setTorque(0.0f);
        }
    }
    void reset() {
        for (auto p : _p) {
            p->reset();
        }
        for (auto p : _rp) {
            p->reset();
        }
    }

    Eigen::VectorXf getPState();
    Eigen::VectorXf getRPState();
    void setPState(Eigen::VectorXf s, float t);
    void setRPState(Eigen::VectorXf s, float t);
    Eigen::VectorXf dParticle();
    Eigen::VectorXf dRParticle();
    void maintainConstraint(float ks, float kd);
    template<class T>void setS(T t){};
    Eigen::VectorXf aParticle() {
        cleanF();
        applyF();
        maintainConstraint(0.0f, 0.0f);
        return dParticle();
    }
    Eigen::VectorXf aRParticle()
    {
        cleanRF();
        applyRF();
        return dRParticle();
    }
    Eigen::VectorXf wallPCollision(Eigen::VectorXf s) {
        for (int i = 0; i < _p.size(); i++) {
            if (s[i * 4] < -0.9f) {
                s[i * 4] = -0.9f;
                s[i * 4 + 2] = -s[i * 4 + 2];
            }
            if (s[i * 4] > 0.9f) {
                s[i * 4] = 0.9f;
                s[i * 4 + 2] = -s[i * 4 + 2];
            }
            if (s[i * 4 + 1] < -0.9f) {
                s[i * 4 + 1] = -0.9f;
                s[i * 4 + 3] = -s[i * 4 + 3];
            }
            if (s[i * 4 + 1] > 0.9f) {
                s[i * 4 + 1] = 0.9f;
                s[i * 4 + 3] = -s[i * 4 + 3];
            }
        }
        return s;
    }
    Eigen::VectorXf wallRPCollision(Eigen::VectorXf s) {
        for (int i = 0; i < _rp.size(); i++) {
            if (s[i * 8] < -(0.9f - _rp[i]->dimension() / 2)) {
                s[i * 8] = -(0.9f - _rp[i]->dimension() / 2);
                s[i * 8 + 3] *= -1;
            }
            if (s[i * 8] > (0.9f - _rp[i]->dimension() / 2)) {
                s[i * 8] = (0.9f - _rp[i]->dimension() / 2);
                s[i * 8 + 3] *= -1;
            }
            if (s[i * 8 + 1] < -(0.9f - _rp[i]->dimension() / 2)) {
                s[i * 8 + 1] = -(0.9f - _rp[i]->dimension() / 2);
                s[i * 8 + 4] *= -1;
            }
            if (s[i * 8 + 1] > (0.9f - _rp[i]->dimension() / 2)) {
                s[i * 8 + 1] = (0.9f - _rp[i]->dimension() / 2);
                s[i * 8 + 4] *= -1;
            }
        }
        return s;
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
    void drawRP() {
        for (auto p : _rp) {
            p->draw();
        }
    }
    void drawUseCase() {
        drawP();
        drawRP();
        drawF();
        drawC();
    }
};

