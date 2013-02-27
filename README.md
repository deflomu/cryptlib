cryptlib
========

Description from the cryptlib website [1]:

> cryptlib is a powerful security toolkit that allows even inexperienced crypto
> programmers to easily add encryption and authentication services to their
> software. The high-level interface provides anyone with the ability to add
> strong security capabilities to an application in as little as half an hour,
> without needing to know any of the low-level details that make the encryption
> or authentication work. Because of this, cryptlib dramatically reduces the
> cost involved in adding security to new or existing applications.
> 
> At the highest level, cryptlib provides implementations of complete security
> services such as S/MIME and PGP/OpenPGP secure enveloping, SSL/TLS and SSH
> secure sessions, CA services such as CMP, SCEP, RTCS, and OCSP, and other
> security operations such as secure timestamping. Since cryptlib uses
> industry-standard X.509, S/MIME, PGP/OpenPGP, and SSH/SSL/TLS data formats,
> the resulting encrypted or signed data can be easily transported to other
> systems and processed there, and cryptlib itself runs on virtually any
> operating system - cryptlib doesn't tie you to a single system. This allows
> email, files, and EDI transactions to be authenticated with digital signatures
> and encrypted in an industry-standard format.
> 
> cryptlib provides an extensive range of other capabilities including full
> X.509/PKIX certificate handling (all X.509 versions from X.509v1 to X.509v3)
> with additional support for SET, Microsoft AuthentiCode, Identrus, SigG,
> S/MIME, SSL, and Qualified certificates, PKCS #7 certificate chains, handling
> of certification requests and CRLs including automated checking of
> certificates against CRLs and online checking using RTCS and OCSP, and issuing
> and revoking certificates using CMP and SCEP. In addition cryptlib implements
> a full range of certification authority (CA) functions, as well as providing
> complete CMP, SCEP, RTCS, and OCSP server implementations to handle online
> certificate enrolment/issue/revocation and certificate status checking.
> Alongside the certificate handling, cryptlib provides a sophisticated key
> storage interface that allows the use of a wide range of key database types
> ranging from PKCS #11 devices, PKCS #15 key files, and PGP/OpenPGP key rings
> through to commercial-grade RDBMS' and LDAP directories with optional SSL
> protection.
> 
> In addition to its built-in capabilities, cryptlib can make use of the crypto
> capabilities of a variety of external crypto devices such as hardware crypto
> accelerators, Fortezza cards, PKCS #11 devices, hardware security modules
> (HSMs), and crypto smart cards. For particularly demanding applications
> cryptlib can be used with a variety of crypto devices that have received
> appropriate FIPS 140 or ITSEC/Common Criteria certification. The crypto device
> interface also provides a convenient general-purpose plug-in capability for
> adding new functionality that will be automatically used by cryptlib.
> 
> cryptlib is supplied as source code for BeOS, DOS, IBM MVS, Macintosh/OS X,
> OS/2, Tandem, a variety of Unix versions (including AIX, Digital Unix, DGUX,
> FreeBSD/NetBSD/OpenBSD, HP-UX, IRIX, Linux, MP-RAS, OSF/1, QNX, SCO/UnixWare,
> Solaris, SunOS, Ultrix, and UTS4), VM/CMS, Windows 3.x, Windows 95/98/ME,
> Windows CE/PocketPC/SmartPhone and Windows NT/2000/XP/Vista/7. cryptlib's
> highly portable nature means that it is also being used in a variety of custom
> embedded system environments including AMX, ChorusOS, eCos, FreeRTOS/OpenRTOS,
> uITRON, MQX, PalmOS, RTEMS, ThreadX, T-Kernel, uC/OS II, VDK, VxWorks, and
> XMK. In addition, cryptlib is available as a standard Windows DLL and an
> ActiveX control. Language bindings are available for C / C++, C# / .NET,
> Delphi, Java, Python, and Visual Basic (VB).

This is the unmodified source code of cryptlib version 3.4.2 with a Xcode
project file added.

See COPYING for license of this source.

[1] http://www.cs.auckland.ac.nz/~pgut001/cryptlib/
