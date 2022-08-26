#include "constraint/RodConstraint.h"
#include <GL/glut.h>

RodConstraint::RodConstraint(Particle *p1, Particle *p2, double dist) :
    _p1(p1), _p2(p2), _dist(dist) {

}

void RodConstraint::draw() {
    glBegin(GL_LINES);
    glColor3f(0.8, 0.7, 0.6);
    glVertex2f(_p1->pos(0), _p1->pos(1));
    glColor3f(0.8, 0.7, 0.6);
    glVertex2f(_p2->pos(0), _p2->pos(1));
    glEnd();
}
