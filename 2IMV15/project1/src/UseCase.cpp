#include "solver/Solver.h"
#include "UseCase.h"


UseCase::UseCase(Solver* solver) : _solver(solver) {}
void UseCase::maintainConstraint(float ks, float kd) {
// Check whether no constraints
    if (_c.empty()) return;

    // Dimension of a particle in the system
    int pDim = 2;
    int pUCSize = _p.size() * pDim;
    // Initiate mass matrix and inverse mass matrix for the system
    Eigen::MatrixXf M = Eigen::MatrixXf::Zero(pUCSize, pUCSize);
    Eigen::MatrixXf W = Eigen::MatrixXf::Zero(pUCSize, pUCSize);
    // Initiate known forces and first time derivative of particles' configuration for the system
    Eigen::VectorXf q = Eigen::VectorXf::Zero(pUCSize);
    Eigen::VectorXf qDot = Eigen::VectorXf::Zero(pUCSize);
    for (int i = 0; i < pUCSize; i += pDim) {
        Particle *p = _p[i/pDim];
        for (int j = 0; j < pDim; j++) {
            q[i+j] = p->f(j);
            qDot[i+j] = p->v(j);
            M(i+j, i+j) = p->m();
            W(i+j, i+j) = 1 / p->m();
        }
    }
    int cUCSize = _c.size();
    // Initiate constraint and first order derivative constraint vector
    Eigen::VectorXf C = Eigen::VectorXf::Zero(cUCSize);
    Eigen::VectorXf CDot = Eigen::VectorXf::Zero(cUCSize);
    // Initiate jacobian, first order derivative jacobian, and the transpose of jacobian matrix
    Eigen::MatrixXf J = Eigen::MatrixXf::Zero(cUCSize, pUCSize);
    Eigen::MatrixXf JDot = Eigen::MatrixXf::Zero(cUCSize, pUCSize);
    Eigen::MatrixXf Jt = Eigen::MatrixXf::Zero(pUCSize, cUCSize);
    for (int i = 0; i < cUCSize; i++) {
        // Obtain a specific constraint from the vector
        Constraint *c = _c[i];
        // Retrieve and store the constraint
        C[i] = c->C();
        // Retrieve and store the the legal velocity of a particular particle
        CDot[i] = c->legalV();
        // Retrieve and store the jacobian vector
        std::vector<Vec2f> jacobian = c->jacobian();
        // Retrieve the first time derivative of the jacobian vector
        std::vector<Vec2f> jacobianDerivative = c->dJacobian();
        std::vector<Particle*> constraintsParticleVector = c->p();
        for (int j = 0; j < constraintsParticleVector.size(); j++) {
            int idx = constraintsParticleVector[j]->ind() * pDim;
            for (int k = 0; k < pDim; k++) {
                JDot(i, idx+k) = jacobianDerivative[j][k];
                J(i, idx+k) = jacobian[j][k];
                Jt(idx+k, i) = jacobian[j][k];
            }
        }
    }
    Eigen::MatrixXf JW = J * W, JWJt = JW * Jt;
    Eigen::VectorXf ksC = ks * C;
    Eigen::VectorXf kdCDot = kd * CDot;
    Eigen::VectorXf JDotqDot = JDot * qDot;
    Eigen::VectorXf JWQ = JW * q;
    // Gather and compute the right hand side object to do conjugate gradient
    Eigen::VectorXf b = -JDotqDot - JWQ - ksC - kdCDot;

    Eigen::ConjugateGradient<Eigen::MatrixXf, Eigen::Lower|Eigen::Upper> cg;
    cg.compute(JWJt);
    Eigen::VectorXf lambda = cg.solve(b);
    // Compute the constraint force Q hat
    Eigen::VectorXf QHat = Jt * lambda;
    for (int i = 0; i < _p.size(); i++) {
        Particle *p = _p[i];
        int idx = pDim * i;
        for (int j = 0; j < pDim; j++) {
            p->updateF(QHat[idx + j], j);
        }
    }
}

Eigen::VectorXf UseCase::getState() {
    Eigen::VectorXf s(this->pDims());
    for (int i = 0; i < _p.size(); i++) {
        s[i * 4 + 0] = _p[i]->pos(0);
        s[i * 4 + 1] = _p[i]->pos(1);
        s[i * 4 + 2] = _p[i]->v(0);
        s[i * 4 + 3] = _p[i]->v(1);
    }
    return s;
}

void UseCase::setState(Eigen::VectorXf s, float t) {
    for (int i = 0; i < _p.size(); i++) {
        _p[i]->setPos(s[i * 4 + 0], 0);
        _p[i]->setPos(s[i * 4 + 1], 1);
        _p[i]->setV(s[i * 4 + 2], 0);
        _p[i]->setV(s[i * 4 + 3], 1);
    }
    _t = t;
}

Eigen::VectorXf UseCase::dParticle() {
    Eigen::VectorXf dst(this->pDims());
    for (int i = 0; i < _p.size(); i++) {
        dst[i * 4 + 0] = _p[i]->v(0);
        dst[i * 4 + 1] = _p[i]->v(1);
        dst[i * 4 + 2] = _p[i]->f(0) / _p[i]->m();
        dst[i * 4 + 3] = _p[i]->f(1) / _p[i]->m();
    }
    return dst;
}

void UseCase::simulationStep() {
    _solver->simulationStep(this);
}
