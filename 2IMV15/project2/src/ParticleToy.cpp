
#include <cmath>
#include <vector>
#include <cstdlib>
#include <cstdio>
#include <GL/glut.h>

#include "imageio.h"
#include "Particle.h"
#include "DemoConstructor.h"
#include "force/MouseForce.h"
#include "solver/EulerSolver.h"

#define IX(i, j) ((i) + (grid_N + 2) * (j))

/* global variables */
static bool mouse_inrigid = false;
static int N;
static float dt, d;
static int dsim;
static int dump_frames;
static int frame_number;

// hyper parameter
float externalF = 0.8f;
static int grid_N;
static float diff, visc;
static float force, source;
static int dvel;
static float *u, *v, *uPrev, *vPrev;
static float *dens, *densPrev;
static int gomx, gomy, gmx, gmy;

// misc
static int win_id;
static int win_x, win_y;
static int mouse_down[3];
static int mouse_release[3];
static int mouse_shiftclick[3];
static int omx, omy, mx, my;
static int hmx, hmy;

// UseCase
UseCase* useCase;
DemoConstructor* demoConstructor;
MouseForce* mouseForce;
Fluid* fluid = new Fluid();


/*
----------------------------------------------------------------------
free/clear/allocate simulation data
----------------------------------------------------------------------
*/

static void free_data() {
    useCase->clean();
    if (u) free(u);
    if (v) free(v);
    if (uPrev) free(uPrev);
    if (vPrev) free(vPrev);
    if (dens) free(dens);
    if (densPrev) free(densPrev);
}

static void clear_data() {
    useCase->reset();
    int size = (grid_N + 2) * (grid_N + 2);
    for (int i = 0; i < size; i++) {
        u[i] = v[i] = uPrev[i] = vPrev[i] = dens[i] = densPrev[i] = 0.0f;
    }
}

static void init_system() {
    useCase = new UseCase(new EulerSolver(EulerSolver::SEMI), fluid);
    demoConstructor = new DemoConstructor();
}

bool allocate_data() {
    int size = (grid_N + 2) * (grid_N + 2);
    u = (float *)malloc(size * sizeof(float));
    v = (float *)malloc(size * sizeof(float));
    uPrev = (float *)malloc(size * sizeof(float));
    vPrev = (float *)malloc(size * sizeof(float));
    dens = (float *)malloc(size * sizeof(float));
    densPrev = (float *)malloc(size * sizeof(float));
    if (!u || !v || !uPrev || !vPrev || !dens || !densPrev) {
        fprintf(stderr, "cannot allocate data\n");
        return false;
    }
    return true;
}

/*
----------------------------------------------------------------------
OpenGL specific drawing routines
----------------------------------------------------------------------
*/

static void pre_display() {
    glViewport(0, 0, win_x, win_y);
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluOrtho2D(-1.0, 1.0, -1.0, 1.0);
    glClearColor(0.0f, 0.0f, 0.0f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);
}

static void post_display() {
	// Write frames if necessary.
    if (dump_frames) {
        const int FRAME_INTERVAL = 4;
        if ((frame_number % FRAME_INTERVAL) == 0) {
            const unsigned int w = glutGet(GLUT_WINDOW_WIDTH);
            const unsigned int h = glutGet(GLUT_WINDOW_HEIGHT);
            auto *buffer = (unsigned char *)malloc(w * h * 4 * sizeof(unsigned char));
            if (!buffer)
                exit(-1);
            glReadPixels(0, 0, w, h, GL_RGBA, GL_UNSIGNED_BYTE, buffer);
            static char filename[80];
            sprintf(filename, "../snapshots/img%.5i.png", frame_number / FRAME_INTERVAL);
            printf("Dumped %s.\n", filename);
            saveImageRGBA(filename, buffer, w, h);
            free(buffer);
        }
    }
    frame_number++;
    glutSwapBuffers();
}

static void draw_velocity() {
    int i, j;
    float x, y, h;
    h = 2.0f / grid_N;
    glColor3f(1.0f, 1.0f, 1.0f);
    glLineWidth(1.0f);
    glBegin(GL_LINES);
    for (i = 1; i <= grid_N; i++) {
        x = (i - 0.5f) * h;
        x = -1 + x;
        for (j = 1; j <= grid_N; j++) {
            y = (j - 0.5f) * h;
            y = -1 + y;
            glVertex2f(x, y);
            glVertex2f(x + u[IX(i, j)], y + v[IX(i, j)]);
        }
    }
    glEnd();
}

static void draw_density() {
    int i, j;
    float x, y, h, d00, d01, d10, d11;
    h = 2.0f / grid_N;
    glBegin(GL_QUADS);
    for (i = 0; i <= grid_N; i++) {
        x = (i - 0.5f) * h;
        x = -1 + x;
        for (j = 0; j <= grid_N; j++) {
            y = (j - 0.5f) * h;
            y = -1 + y;
            d00 = dens[IX(i, j)];
            d01 = dens[IX(i, j + 1)];
            d10 = dens[IX(i + 1, j)];
            d11 = dens[IX(i + 1, j + 1)];
            glColor3f(d00, d00, d00);
            glVertex2f(x, y);
            glColor3f(d10, d10, d10);
            glVertex2f(x + h, y);
            glColor3f(d11, d11, d11);
            glVertex2f(x + h, y + h);
            glColor3f(d01, d01, d01);
            glVertex2f(x, y + h);
        }
    }
    glEnd();
}

/*
----------------------------------------------------------------------
relates mouse movements to particle toy construction
----------------------------------------------------------------------
*/

static void get_from_UI_particle() {
    int i, j;
    int hi, hj;
    if (!mouse_down[0] && !mouse_down[2] && !mouse_release[0] && !mouse_shiftclick[0] && !mouse_shiftclick[2])
        return ;
    i = (int)((mx / (float)win_x) * N);
    j = (int)(((win_y - my) / (float)win_y) * N);
    if (i < 1 || i > N || j < 1 || j > N)
        return ;
    if (mouse_down[0]) {
    }
    if (mouse_down[2]) {
    }
    hi = (int)((hmx / (float)win_x) * N);
    hj = (int)(((win_y - hmy) / (float)win_y) * N);
    if (mouse_release[0]) {
    }
    omx = mx;
    omy = my;
}

static void get_from_UI_grid(float* _d, float* _u, float* _v) {
    int i, j, size = (grid_N + 2) * (grid_N + 2);
    for (i = 0; i < size; i++) {
        _u[i] = _v[i] = _d[i] = 0.0f;
    }
    if (!mouse_down[0] && !mouse_down[2])
        return ;
    i = (int)((gmx / (float)win_x) * grid_N + 1);
    j = (int)(((win_y - gmy) / (float)win_y) * grid_N + 1);
    if (i < 1 || i > grid_N || j < 1 || j > grid_N)
        return;
    if (mouse_down[0] && !mouse_inrigid) {
        _u[IX(i, j)] = force * (gmx - gomx);
        _v[IX(i, j)] = force * (gomy - gmy);
    }
    if (mouse_down[2] && !mouse_inrigid) {
        _d[IX(i, j)] = source;
    }
    gomx = gmx;
    gomy = gmy;
}

static void remap_GUI() {
    for (auto p : useCase->p()) {
        p->setPos(p->initPos());
    }
}

/*
----------------------------------------------------------------------
GLUT callback routines
----------------------------------------------------------------------
*/

static void key_func(unsigned char key, int x, int y) {
	switch (key) {
        case '0':
            clear_data();
            if (dsim)
                dsim = !dsim;
            init_system();
            demoConstructor->DummyToy(useCase);
            break;
        case '1':
            clear_data();
            if (dsim)
                dsim = !dsim;
            init_system();
            demoConstructor->FixedObject(useCase, fluid);
            break;
        case '2':
            clear_data();
            if (dsim)
                dsim = !dsim;
            init_system();
            demoConstructor->MovingSolid(useCase, fluid);
            break;
        case '3':
            clear_data();
            if (dsim)
                dsim = !dsim;
            init_system();
            demoConstructor->MovingRigid(useCase, fluid);
            break;
        case '4':
            clear_data();
            if (dsim)
                dsim = !dsim;
            init_system();
            demoConstructor->Collision2R(useCase, fluid);
            break;
        case '5':
            clear_data();
            if (dsim)
                dsim = !dsim;
            init_system();
            externalF = 0.001f;
            demoConstructor->Cloth2D(useCase);
            break;
        case 'c':
        case 'C':
            clear_data ();
            break;
        case 'd':
        case 'D':
            dump_frames = !dump_frames;
            break;
        case 'v':
        case 'V':
            dvel = !dvel;
            break;
        case 'q':
        case 'Q':
            free_data();
            exit(0);
            break;
        case ' ':
            dsim = !dsim;
            if (dsim)
                useCase->reset();
            break;
        default:
            break;
	}
}

static void mouse_func(int button, int state, int x, int y) {
    if (mouse_down[button])
        mouse_release[button] = state == GLUT_UP;
    if (mouse_down[button])
        mouse_shiftclick[button] = glutGetModifiers() == GLUT_ACTIVE_SHIFT;
    mouse_down[button] = state == GLUT_DOWN;
    if (state == GLUT_UP) {
        mouseForce->setActive(false);
        mouse_inrigid = false;
    } else {
        float mouse_x = (x - int(win_x / 2));
        float mouse_y = (int(win_y / 2) - y);
        mouse_x = mouse_x / (win_x / 2);
        mouse_y = mouse_y / (win_y / 2);
        Particle *closestP = nullptr;
        for (int i = 0; i < useCase->rp().size(); i++) {
            Eigen::Vector2f position = useCase->rp(i)->massCenter();
            float r = useCase->rp(i)->dimension();
            r = r / 2 * 1.1;
            float distance = std::sqrt((mouse_x - position[0]) * (mouse_x - position[0]) + (mouse_y - position[1]) * (mouse_y - position[1]));
            if (distance < r) {
                mouse_inrigid = true;
                closestP = useCase->rp(i);
            }
        }
        mouseForce = new MouseForce(closestP, Eigen::Vector2f(0.0f, 0.0f), externalF);
        if (closestP != nullptr) {
            useCase->addRigidForce(mouseForce);
        }
    }
    gomx = x;
    gomy = y;
    gmx = x;
    gmy = y;
}

static void motion_func(int x, int y) {
    float fx = x - (win_x / 2);
    float fy = (win_y / 2) - y;
    fx = fx / (win_x / 2);
    fy = fy / (win_y / 2);
    if (mouse_inrigid) {
        Eigen::Vector2f position = mouseForce->pp()->massCenter();
        mouseForce->setDirection(10000.0f * Eigen::Vector2f(fx - position[0], fy - position[1]));
    }
    gmx = x;
    gmy = y;
}

static void reshape_func(int width, int height) {
	glutSetWindow ( win_id );
	glutReshapeWindow ( width, height );
	win_x = width;
	win_y = height;
}

static void idle_func() {
    fluid->setRParticle(useCase->rp());
    if (dsim) {
        useCase->simulationStep();
    } else {
        get_from_UI_particle();
        remap_GUI();
    }
    get_from_UI_grid(densPrev, uPrev, vPrev);
    fluid->velStep(grid_N, u, v, uPrev, vPrev, visc, dt);
    fluid->densStep(grid_N, dens, densPrev, u, v, diff, dt);
    fluid->vorticityConfinement(grid_N, dt, densPrev, u, v, uPrev, vPrev);
	glutSetWindow(win_id);
	glutPostRedisplay();
}

static void display_func() {
    pre_display();
    if (dvel)
        draw_velocity();
    else
        draw_density();
    useCase->drawUseCase();
    post_display(); //frame,img
}


/*
----------------------------------------------------------------------
open_glut_window --- open a glut compatible window and set callbacks
----------------------------------------------------------------------
*/

static void open_glut_window(){
	glutInitDisplayMode ( GLUT_RGBA | GLUT_DOUBLE );
	glutInitWindowPosition ( 0, 0 );
	glutInitWindowSize ( win_x, win_y );
	win_id = glutCreateWindow ( "Particletoys!" );
	glClearColor ( 0.0f, 0.0f, 0.0f, 1.0f );
	glClear ( GL_COLOR_BUFFER_BIT );
	glutSwapBuffers ();
	glClear ( GL_COLOR_BUFFER_BIT );
	glutSwapBuffers ();
	glEnable(GL_LINE_SMOOTH);
	glEnable(GL_POLYGON_SMOOTH);
	pre_display ();
	glutKeyboardFunc ( key_func );
	glutMouseFunc ( mouse_func );
	glutMotionFunc ( motion_func );
	glutReshapeFunc ( reshape_func );
	glutIdleFunc ( idle_func );
	glutDisplayFunc ( display_func );
}


/*
----------------------------------------------------------------------
main --- main routine
----------------------------------------------------------------------
*/

int main(int argc, char ** argv) {
	glutInit(&argc, argv);
    dsim = 0;
    dump_frames = 0;
    frame_number = 0;
    win_x = 1024;
    win_y = 1024;
    dvel = 1;
	if (argc == 1) {
		N = 64;
		dt = 0.1f;
		d = 5.f;
        grid_N = 128;
        diff = 0.0f;
        visc = 0.0f;
        force = 5.0f;
        source = 100.0f;
	} else {
		N = atoi(argv[1]);
		dt = atof(argv[2]);
		d = atof(argv[3]);
	}
	printf("\n\nHow to use this application:\n\n");
	printf("\t Toggle construction/simulation display with the spacebar key\n");
	printf("\t Dump frames by pressing the 'd' key\n");
    printf("\t Quit by pressing the 'q' key\n\n");
    printf("\t [Press 1] --- Fixed Objects\n");
    printf("\t [Press 2] --- Moving Solid\n");
    printf("\t [Press 3] --- Moving Rigid\n");
    printf("\t [Press 4] --- Colliding contact\n");
    printf("\t [Press 5] --- Cloth in fluid\n");

    init_system();
    assert(allocate_data());
    clear_data();
	open_glut_window();
	glutMainLoop();

    exit(0);
}

