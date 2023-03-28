// Sets a listening socket on host.
#include <err.h>
#include <sys/socket.h>
#include <unistd.h>

#include <cstdio>
#include <cstdlib>

// Needs to be included after sys/socket.h
#include <linux/vm_sockets.h>

constexpr int kPort = 1221;

int main(int argc, const char *argv[]) {
  int server_fd(socket(AF_VSOCK, SOCK_STREAM, 0));
  if (server_fd < 0) {
    errx(EXIT_FAILURE, "failed to set up the socket");
  }

  struct sockaddr_vm server_sa = (struct sockaddr_vm){
      .svm_family = AF_VSOCK,
      .svm_port = kPort,
      .svm_cid = VMADDR_CID_ANY,
  };

  int ret = bind(server_fd, (struct sockaddr *)&server_sa, sizeof(server_sa));
  if (ret != 0) {
    errx(EXIT_FAILURE, "failed to bind to the address");
  }
  ret = listen(server_fd, 1);
  if (ret != 0) {
    errx(EXIT_FAILURE, "failed to listen to port %d", kPort);
  }

  printf("Listening for connections on port %d...\n", kPort);
  struct sockaddr_vm client_sa;
  socklen_t client_sa_len = sizeof(client_sa);
  int client_fd =
      accept(server_fd, (struct sockaddr *)&client_sa, &client_sa_len);
  if (client_fd < 0) {
    errx(EXIT_FAILURE, "failed to get the client fd");
  }

  char buffer[64];
  // Receive data from the client
  if (recv(client_fd, buffer, sizeof(buffer), 0) == -1) {
    errx(EXIT_FAILURE, "failed to receive");
  }

  printf("Received: %s\n", buffer);
  close(server_fd);
  close(client_fd);

  return EXIT_SUCCESS;
}