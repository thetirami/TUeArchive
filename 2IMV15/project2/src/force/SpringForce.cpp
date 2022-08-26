#include "force/SpringForce.h"
#include <GL/glut.h>

SpringForce::SpringForce(Particle *p1, Particle *p2, double dist, double ks, double kd) : _p1(p1), _p2(p2), _dist(dist), _ks(ks), _kd(kd) {}

void SpringForce::draw() {
    glBegin(GL_LINES);
    glColor3f(0.8, 0.7, 0.2);
    glVertex2f(_p1->pos(0), _p1->pos(1));
    glColor3f(0.8, 0.7, 0.2);
    glVertex2f(_p2->pos(0), _p2->pos(1));
    glEnd();
}

void SpringForce::apply() {
    Eigen::Vector2f l = _p1->pos() - _p2->pos();
    Eigen::Vector2f dl = _p1->v() - _p2->v();
    if (isActive()) {
        Eigen::Vector2f force = (_ks*(l.norm()-_dist)+_kd*(l.dot(dl)/l.norm()))*(l/l.norm());
        _p1->updateF(-force);
        _p2->updateF( force);
    }
}
