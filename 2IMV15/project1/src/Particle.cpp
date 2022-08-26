#include "Particle.h"
#include <GL/glut.h>

Particle::Particle(const Vec2f &ConstructPos, double m, int ind) :
    _initPos(ConstructPos), _pos(Vec2f(0.0f, 0.0f)), _v(Vec2f(0.0, 0.0)), _m(m), _ind(ind) {
}

Particle::~Particle() = default;

void Particle::reset() {
	_pos = _initPos;
	_v = Vec2f(0.0, 0.0);
	_f = Vec2f(0.0, 0.0);
}
void Particle::draw() {
    const float h = 6.f;
    glColor3f(1.f, 1.f, 1.f); //rgb
    glPointSize(h);
    glBegin(GL_POINTS);
    glVertex2f(_pos[0], _pos[1]);
    glEnd();
}
