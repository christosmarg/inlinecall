# $FreeBSD$

PROG=		inlinecall
SRCS=		${PROG}.c
MAN=		${PROG}.1
LDFLAGS+=	-ldwarf -lelf

.include <bsd.prog.mk>
